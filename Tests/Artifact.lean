import LeanTex.Cli.FontDiscovery
import Tests.Backends

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open LeanTex.Core.PdfRead (Obj Entry)

/-! # The artifact tier: what the produced bytes paint, and where

`censusChecks` reads `Layout.Out` — the engine's own record of what it
decided to ship. This tier reads the *file*: the page's `/MediaBox`, its
content stream's operators, the glyph widths in the descendant font's
`/W`, the characters in its `/ToUnicode`, the ascent and descent in its
`/FontDescriptor`. Nothing here consults a `LineOut`, so a layout that
records one position and paints another is a failure here and a pass
there — which is the gap this tier exists to close: a private reference
deck once matched its reference output on none of its pages while the
whole suite was green, and every defect behind that number was found by
rasterising a page or reading its text layer.

The reading is a PDF-semantics evaluation, not a search for the writer's
spellings: a text object's pen starts at `Tm`, advances by each glyph's
`/W` width scaled by `Tf` size and `Tz` horizontal scale, and steps by
each `TJ` adjustment under §9.4.4's rule. A run's box is that advance
horizontally and the descriptor's ascent and descent vertically. So a
defect that moves ink without changing the writer's vocabulary — a
negative coordinate, a collapsed picture, a repeated page — is visible
here by the same arithmetic a viewer performs.

The one thing this tier takes from outside the file is the *declared*
geometry (`Layout.Geom.ofPage`): margins, page size, furniture bands.
That is an input to the build — what the document asked for — not a
reading of what the engine believes it produced, and the distinction is
what keeps the tier independent. Where the region is a fact of the
artifact (the page box, a painted title band) it is read from the bytes.
-/

/-- One token of a content stream (ISO 32000-2 §7.2). Numbers carry their
value in sp — parsed by the engine's own reader (`Obj.sp?`), so a
coordinate here means what it means in a page dictionary — beside their
raw spelling, which the integer operands (a `TJ` adjustment, an `/MCID`)
read. -/
inductive CTok where
  | num (v : Dim.Sp) (raw : String)
  | name (n : String)
  /-- A hexadecimal string's digits, whitespace removed. -/
  | hex (digits : String)
  /-- A literal string's bytes, one backslash escape resolved per byte. -/
  | lit (raw : String)
  | arrOpen
  | arrClose
  | dictOpen
  | dictClose
  | op (name : String)
  deriving Repr, BEq, Inhabited

private def ctWs (c : Nat) : Bool :=
  c == 0 || c == 9 || c == 10 || c == 12 || c == 13 || c == 32

private def ctDelim (c : Nat) : Bool :=
  c == 40 || c == 41 || c == 60 || c == 62 || c == 91 || c == 93 ||
    c == 123 || c == 125 || c == 47 || c == 37

private def ctAt (b : ByteArray) (i : Nat) : Nat :=
  (b[i]?.map (·.toNat)).getD 256

private def ctNumByte (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || c == 43 || c == 45 || c == 46

/-- A content stream's tokens, in order. Index-bounded throughout: the
outer loop's bound is the byte count and every step advances `i`, so the
walk terminates by structure alone. Comments and whitespace are dropped;
everything else becomes exactly one token, so an operator's operands are
the tokens since the last operator. -/
def scanContent (b : ByteArray) : Array CTok := Id.run do
  let mut out : Array CTok := #[]
  let mut i := 0
  for _ in [0:b.size + 1] do
    if b.size ≤ i then break
    let c := ctAt b i
    if ctWs c then
      i := i + 1
    else if c == 37 then
      let mut j := i + 1
      for _ in [0:b.size + 1] do
        let d := ctAt b j
        if d == 256 || d == 10 || d == 13 then break
        j := j + 1
      i := j
    else if c == 47 then
      let mut j := i + 1
      let mut s := ""
      for _ in [0:b.size + 1] do
        let d := ctAt b j
        if d == 256 || ctWs d || ctDelim d then break
        s := s.push (Char.ofNat d)
        j := j + 1
      out := out.push (.name s)
      i := j
    else if c == 60 then
      if ctAt b (i + 1) == 60 then
        out := out.push .dictOpen
        i := i + 2
      else
        let mut j := i + 1
        let mut s := ""
        for _ in [0:b.size + 1] do
          let d := ctAt b j
          if d == 256 || d == 62 then break
          unless ctWs d do s := s.push (Char.ofNat d)
          j := j + 1
        out := out.push (.hex s)
        i := j + 1
    else if c == 62 then
      if ctAt b (i + 1) == 62 then
        out := out.push .dictClose
        i := i + 2
      else
        i := i + 1
    else if c == 91 then
      out := out.push .arrOpen
      i := i + 1
    else if c == 93 then
      out := out.push .arrClose
      i := i + 1
    else if c == 40 then
      let mut j := i + 1
      let mut depth := 1
      let mut s := ""
      for _ in [0:b.size + 1] do
        let d := ctAt b j
        if d == 256 then break
        if d == 92 then
          s := s.push (Char.ofNat (ctAt b (j + 1)))
          j := j + 2
        else if d == 40 then
          depth := depth + 1
          s := s.push '('
          j := j + 1
        else if d == 41 then
          depth := depth - 1
          j := j + 1
          if depth == 0 then break
          s := s.push ')'
        else
          s := s.push (Char.ofNat d)
          j := j + 1
      out := out.push (.lit s)
      i := j
    else if ctNumByte c then
      let mut j := i
      let mut s := ""
      for _ in [0:b.size + 1] do
        let d := ctAt b j
        if ctNumByte d then
          s := s.push (Char.ofNat d)
          j := j + 1
        else break
      out := out.push (.num ((Obj.real s).sp?.getD 0) s)
      i := j
    else
      let mut j := i
      let mut s := ""
      for _ in [0:b.size + 1] do
        let d := ctAt b j
        if d == 256 || ctWs d || ctDelim d then break
        s := s.push (Char.ofNat d)
        j := j + 1
      out := out.push (.op s)
      i := j
  return out

private def artHexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- A hexadecimal string read as two-byte codes: the CIDs an Identity-H
string spells (§9.7.4.2), and the code units a `/ToUnicode` value
spells. -/
def artCodes (digits : String) : Array Nat := Id.run do
  let cs := digits.toList.toArray
  let mut out : Array Nat := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if cs.size < i + 4 then break
    let nib (k : Nat) : Nat := (artHexNibble (cs[k]!)).getD 0
    out := out.push ((((nib i) * 16 + nib (i + 1)) * 16 + nib (i + 2)) * 16 + nib (i + 3))
    i := i + 4
  return out

/-- A `/ToUnicode` value as text: UTF-16BE code units, surrogate pairs
joined (§9.10.3). -/
def artUtf16 (digits : String) : String := Id.run do
  let us := artCodes digits
  let mut out := ""
  let mut i := 0
  for _ in [0:us.size + 1] do
    if us.size ≤ i then break
    let u := us[i]!
    if 0xD800 ≤ u && u ≤ 0xDBFF && i + 1 < us.size then
      out := out.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (us[i + 1]! - 0xDC00)))
      i := i + 2
    else
      out := out.push (Char.ofNat u)
      i := i + 1
  return out

/-- One face as the *file* describes it: the CID-to-character map its
`/ToUnicode` CMap spells, the widths its `/W` array spells (thousandths
of the em), and the vertical extent its `/FontDescriptor` declares. The
only reading of a glyph's identity and size this tier performs. -/
structure ArtFont where
  toUni : Std.HashMap Nat String
  /-- Glyph advances, in thousandths of the em times `Dim.spPerPt` — the
  units `artMille` reads. -/
  widths : Std.HashMap Nat Int
  defaultWidth : Int
  ascent : Int
  descent : Int
  /-- `/CapHeight`: the height a line of text measures from its glyphs.
  The engine judges its own text area against this rather than `/Ascent`
  (`Font.inkAscent`, and `Check.Shipped.ofOut`'s stated reason: the hhea
  ascent reserves accent headroom that is usually blank), so the artifact
  tier reads the file's declaration of the same quantity. -/
  capHeight : Int
  deriving Inhabited

/-- The `bfchar` pairs of a `/ToUnicode` CMap: CID, then its text. -/
def artToUniMap (toks : Array CTok) : Std.HashMap Nat String := Id.run do
  let mut m : Std.HashMap Nat String := {}
  let mut inBf := false
  let mut pend : Option String := none
  for t in toks do
    match t with
    | .op "beginbfchar" =>
      inBf := true
      pend := none
    | .op "endbfchar" =>
      inBf := false
      pend := none
    | .hex d =>
      if inBf then
        match pend with
        | none => pend := some d
        | some g =>
          m := m.insert ((artCodes g)[0]?.getD 0) (artUtf16 d)
          pend := none
    | _ => pure ()
  return m

/-- A metric in a font dictionary, read exactly: thousandths of the em
scaled by `Dim.spPerPt`, which is the unit every field of `ArtFont`
carries.

Not `Obj.int?`. A PDF number object may be real — lualatex writes
`/W [0 [552.734 …]]` — and truncating each entry to an integer thousandth
loses up to 0.001 em per glyph, 0.44 bp across a 60-glyph line at 10 bp,
which is the scale a placement claim measures at. `Obj.sp?` is the
repository's own exact reader for both spellings, and scaling the
numerator and the denominator of an advance by the same `Dim.spPerPt`
leaves an integer-valued file's reading unchanged to the sp. -/
def artMille (o : Obj) : Option Int := o.sp?

/-- A `/W` array (§9.7.4.3), both forms: `c [w …]` and `c1 c2 w`. The
range form is capped so a malformed pair cannot make the reading
unbounded. -/
def artWidthMap (o : Obj) : Std.HashMap Nat Int := Id.run do
  let mut m : Std.HashMap Nat Int := {}
  let .arr xs := o | return m
  let mut i := 0
  for _ in [0:xs.size + 1] do
    if xs.size ≤ i then break
    match xs[i]!, xs[i + 1]? with
    | .int c, some (.arr ws) =>
      for k in [0:ws.size] do
        if let some w := artMille ws[k]! then m := m.insert (c.toNat + k) w
      i := i + 2
    | .int c1, some (.int c2) =>
      match (xs[i + 2]?).bind artMille with
      | some w =>
        if c1 ≤ c2 && c2 - c1 ≤ 65535 then
          for g in [c1.toNat:c2.toNat + 1] do m := m.insert g w
        i := i + 3
      | _ => i := i + 1
    | _, _ => i := i + 1
  return m

/-- A Type0 font dictionary read as an `ArtFont`: its `/ToUnicode` stream
decoded and scanned, its descendant's `/W` and `/DW`, its descriptor's
`/Ascent` and `/Descent`.

Every composite value is dereferenced. lualatex writes `/W` as an
indirect reference to an object of its own; read without the deref it is
a `.ref`, `artWidthMap` sees no array, and every glyph on the page takes
`/DW` — a page of prose then reads one em per glyph and no placement
claim about it means anything. -/
def artFontOf (es : Array Entry) (o : Obj) : ArtFont :=
  let deref := PdfCensus.deref es
  let toUni := match o.get? "ToUnicode" with
    | some (.ref n _) =>
      match es.find? (·.num == n) with
      | some e =>
        match e.decoded with
        | .ok (some data) => artToUniMap (scanContent data)
        | _ => {}
      | none => {}
    | _ => {}
  let cid := match deref ((o.get? "DescendantFonts").getD .null) with
    | .arr xs => deref (xs[0]?.getD .null)
    | d => d
  let fd := deref ((cid.get? "FontDescriptor").getD .null)
  let milleOf (d : Obj) (k : String) (dflt : Int) : Int :=
    (((d.get? k).map deref).bind artMille).getD dflt
  { toUni
    widths := artWidthMap (deref ((cid.get? "W").getD .null))
    defaultWidth := milleOf cid "DW" (1000 * Dim.spPerPt)
    ascent := milleOf fd "Ascent" (1000 * Dim.spPerPt)
    descent := milleOf fd "Descent" (-300 * Dim.spPerPt)
    capHeight := milleOf fd "CapHeight" (milleOf fd "Ascent" (1000 * Dim.spPerPt)) }

/-- The marked-content sequence a painting operator stands inside
(§14.6). Real content carries the structure type the writer gave it and
its identifier on the page; an artifact carries its declared type, or
none. The distinction is what lets a claim say "no *body* ink here"
about a region running furniture legitimately occupies. -/
inductive ArtMark where
  | artifact (kind : Option String)
  | content (tag : String) (mcid : Nat)
  deriving Repr, BEq, Inhabited

def ArtMark.isArtifact : ArtMark → Bool
  | .artifact _ => true
  | .content _ _ => false

def ArtMark.render : ArtMark → String
  | .artifact none => "/Artifact"
  | .artifact (some k) => s!"/Artifact /{k}"
  | .content t n => s!"/{t} /MCID {n}"

/-- One glyph run the file paints: the pen where `Tm` and the preceding
`TJ` elements put it, the advance its glyphs' own widths give it, and the
text its `/ToUnicode` map spells. Nothing is read from layout. -/
structure ArtRun where
  marks : Array ArtMark
  x : Dim.Sp
  y : Dim.Sp
  w : Dim.Sp
  size : Dim.Sp
  /-- The face's declared `/Ascent` at this size: the generous box, which
  the page-box claim reads. -/
  ascent : Dim.Sp
  /-- The face's declared `/CapHeight` at this size: the measure the
  engine judges its own text area by. -/
  inkAscent : Dim.Sp
  descent : Dim.Sp
  /-- The widest advance among this run's own glyphs. Character
  protrusion hangs a boundary glyph into the margin by at most its own
  advance (`Layout.protrusionLR_covers` bounds the factor by 1000‰), so
  this is the declared slack a text-area claim must allow — read from the
  file's `/W`, not from a constant. -/
  widest : Dim.Sp
  text : String
  /-- Where each of this run's glyphs starts, and what it spells: the pen
  before that glyph's own advance, in PDF user space, paired with the text
  its `/ToUnicode` gives it.

  A run is not a comparable unit across writers — the engine emits a run
  per hyphenation opportunity and lualatex one per kern pair, 23 against
  17 on one measured line of identical text — so a placement claim has to
  reach the glyph. Defaulted, because every claim that reads whole runs
  predates it. -/
  glyphs : Array (Dim.Sp × String) := #[]
  /-- The font resource the run's `Tf` named — which face the run is in, as
  the file says it, so a claim can find where one face gives way to the
  next. Defaulted like `glyphs`. -/
  face : String := ""
  deriving Repr, Inhabited

/-- One non-text mark the file paints, as its bounding box in PDF user
space: a fill, a stroked or filled path, an image, or the outlined box
standing where an image did not load. -/
structure ArtBox where
  marks : Array ArtMark
  kind : String
  x0 : Dim.Sp
  y0 : Dim.Sp
  x1 : Dim.Sp
  y1 : Dim.Sp
  deriving Repr, Inhabited

def ArtRun.x1 (r : ArtRun) : Dim.Sp := r.x + r.w

/-- A run's top edge under the generous box: the baseline plus the
declared `/Ascent` at the set size. -/
def ArtRun.top (r : ArtRun) : Dim.Sp := r.y + r.ascent

/-- A run's top edge under the engine's own ink measure: the baseline plus
the declared `/CapHeight`. -/
def ArtRun.inkTop (r : ArtRun) : Dim.Sp := r.y + r.inkAscent

/-- A run's bottom edge: the baseline plus the descriptor's descent
(negative) at the set size. -/
def ArtRun.bottom (r : ArtRun) : Dim.Sp := r.y + r.descent

def ArtRun.isArtifact (r : ArtRun) : Bool := r.marks.any ArtMark.isArtifact

def ArtBox.isArtifact (b : ArtBox) : Bool := b.marks.any ArtMark.isArtifact

private def ctName? : CTok → Option String
  | .name n => some n
  | _ => none

/-- The name following `/key` among an operator's operands: how `/Type`
is read out of an artifact's property dictionary. -/
private def artNameAfter (stack : Array CTok) (key : String) : Option String := do
  let i ← stack.findIdx? (· == CTok.name key)
  (stack[i + 1]?).bind ctName?

private def artIntAfter (stack : Array CTok) (key : String) : Option Int := do
  let i ← stack.findIdx? (· == CTok.name key)
  match stack[i + 1]? with
  | some (.num _ raw) => raw.toInt?
  | _ => none

/-- The state the evaluation threads: the marked-content stack, the pen,
the face and size in force, the horizontal scale in per mille, the open
path's box, and the transformation the last `cm` set (for `Do`). -/
private structure ArtSt where
  runs : Array ArtRun := #[]
  boxes : Array ArtBox := #[]
  marks : Array ArtMark := #[]
  stack : Array CTok := #[]
  x : Dim.Sp := 0
  y : Dim.Sp := 0
  size : Dim.Sp := 0
  th : Int := 1000
  font : Option ArtFont := none
  face : String := ""
  path : Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := none
  cm : Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := none

private def artExtend (p : Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp))
    (x y : Dim.Sp) : Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
  match p with
  | none => some (x, y, x, y)
  | some (x0, y0, x1, y1) => some (min x0 x, min y0 y, max x1 x, max y1 y)

/-- The numeric operands of an operator, in order. -/
private def artNums (stack : Array CTok) : Array Dim.Sp :=
  stack.filterMap fun t => match t with
    | .num v _ => some v
    | _ => none

/-- The painting operators that put ink on the page (§8.5.3, Table 60);
`n` ends a path without painting and is not among them. -/
private def artPaintOps : List String :=
  ["f", "F", "f*", "B", "B*", "b", "b*", "S", "s"]

/-- The face a `TJ` with no `Tf` in force would set in: none, spelled so
a malformed stream's ink is still recorded rather than silently dropped —
its glyphs read as unmapped and its box as zero-height. -/
def artNoFont : ArtFont :=
  { toUni := {}, widths := {}, defaultWidth := 1000 * Dim.spPerPt, ascent := 0
    descent := 0, capHeight := 0 }

/-- What a CID with no `/ToUnicode` entry reads as: U+FFFD, so an
unmapped glyph is visible to a text claim rather than silently absent. -/
def artUnmapped : String := String.singleton (Char.ofNat 0xFFFD)

/-- What a content stream paints, evaluated: every glyph run with its own
box, and every fill, path and image with theirs. The arithmetic is
§9.4.4's — the pen advances by each glyph's width times the size times
the horizontal scale, and a `TJ` number displaces it by `-d/1000` of the
same — so the positions are a viewer's, not the writer's record of its
intent. -/
def evalContent (fonts : Std.HashMap String ArtFont) (toks : Array CTok) :
    Array ArtRun × Array ArtBox := Id.run do
  let mut s : ArtSt := {}
  for t in toks do
    match t with
    | .op o =>
      let ns := artNums s.stack
      if o == "BT" then
        s := { s with x := 0, y := 0 }
      else if o == "Tm" then
        if 6 ≤ ns.size then s := { s with x := ns[4]!, y := ns[5]! }
      else if o == "Td" then
        if 2 ≤ ns.size then s := { s with x := s.x + ns[0]!, y := s.y + ns[1]! }
      else if o == "Tf" then
        let nm := (s.stack.findSome? ctName?).getD ""
        s := { s with font := fonts[nm]?, face := nm, size := (ns[0]?).getD s.size }
      else if o == "Tz" then
        -- The operand is a percentage; the scale is kept in per mille,
        -- rounded: `98.7` reads 6468403 sp, which truncates to 986.
        s := { s with th := (((ns[0]?).getD (Dim.pt 100)) * 10 + Dim.spPerPt / 2) / Dim.spPerPt }
      else if o == "TJ" || o == "Tj" then
        for it in s.stack do
          match it with
          | .hex d =>
            let f := s.font.getD artNoFont
            let cids := artCodes d
            let mut adv : Dim.Sp := 0
            let mut widest : Dim.Sp := 0
            let mut txt := ""
            let mut gs : Array (Dim.Sp × String) := #[]
            for g in cids do
              let one := (f.widths[g]?.getD f.defaultWidth) * s.size * s.th
                / (1000000 * Dim.spPerPt)
              gs := gs.push (s.x + adv, f.toUni[g]?.getD artUnmapped)
              adv := adv + one
              widest := max widest one
              txt := txt ++ (f.toUni[g]?.getD artUnmapped)
            s := { s with
              runs := s.runs.push
                { marks := s.marks, x := s.x, y := s.y, w := adv, size := s.size,
                  ascent := f.ascent * s.size / (1000 * Dim.spPerPt),
                  inkAscent := f.capHeight * s.size / (1000 * Dim.spPerPt),
                  descent := f.descent * s.size / (1000 * Dim.spPerPt)
                  widest := widest, text := txt, glyphs := gs, face := s.face }
              x := s.x + adv }
          | .num _ raw =>
            let d := raw.toInt?.getD 0
            s := { s with x := s.x - d * s.size * s.th / 1000000 }
          | _ => pure ()
      else if o == "m" || o == "l" then
        if 2 ≤ ns.size then s := { s with path := artExtend s.path ns[0]! ns[1]! }
      else if o == "c" then
        if 6 ≤ ns.size then
          let mut p := s.path
          for k in [0:3] do p := artExtend p (ns[2 * k]!) (ns[2 * k + 1]!)
          s := { s with path := p }
      else if o == "v" || o == "y" then
        if 4 ≤ ns.size then
          let mut p := s.path
          for k in [0:2] do p := artExtend p (ns[2 * k]!) (ns[2 * k + 1]!)
          s := { s with path := p }
      else if o == "re" then
        if 4 ≤ ns.size then
          let p := artExtend s.path (ns[0]!) (ns[1]!)
          s := { s with path := artExtend p (ns[0]! + ns[2]!) (ns[1]! + ns[3]!) }
      else if artPaintOps.contains o then
        if let some (x0, y0, x1, y1) := s.path then
          let kind := if o == "S" || o == "s" then "stroke" else "fill"
          s := { s with
            boxes := s.boxes.push { marks := s.marks, kind := kind
                                    x0 := x0, y0 := y0, x1 := x1, y1 := y1 }
            path := none }
      else if o == "n" then
        s := { s with path := none }
      else if o == "cm" then
        if 6 ≤ ns.size then s := { s with cm := some (ns[0]!, ns[3]!, ns[4]!, ns[5]!) }
      else if o == "Do" then
        if let some (a, d, e, f) := s.cm then
          s := { s with
            boxes := s.boxes.push { marks := s.marks, kind := "image"
                                    x0 := min e (e + a), y0 := min f (f + d)
                                    x1 := max e (e + a), y1 := max f (f + d) } }
      else if o == "q" || o == "Q" then
        s := { s with cm := none }
      else if o == "BMC" || o == "BDC" then
        let tag := (s.stack.findSome? ctName?).getD ""
        let m : ArtMark := if tag == "Artifact" then .artifact (artNameAfter s.stack "Type")
          else .content tag ((artIntAfter s.stack "MCID").getD 0).toNat
        s := { s with marks := s.marks.push m }
      else if o == "EMC" then
        s := { s with marks := s.marks.pop }
      s := { s with stack := #[] }
    | other => s := { s with stack := s.stack.push other }
  return (s.runs, s.boxes)

/-- One page as the file describes it: its declared media box, the faces
its resources name, its content stream's bytes, and the ink those bytes
paint. -/
structure ArtPage where
  media : Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp
  runs : Array ArtRun
  boxes : Array ArtBox
  content : ByteArray
  deriving Inhabited

def ArtPage.mediaW (p : ArtPage) : Dim.Sp := p.media.2.2.1 - p.media.1

def ArtPage.mediaH (p : ArtPage) : Dim.Sp := p.media.2.2.2 - p.media.2.1

/-- A rectangle array read in sp, or the null rectangle. -/
private def artRect (o : Obj) : Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp :=
  match o with
  | .arr xs =>
    let v (k : Nat) : Dim.Sp := ((xs[k]?).bind Obj.sp?).getD 0
    (v 0, v 1, v 2, v 3)
  | _ => (0, 0, 0, 0)

/-- Every page a file carries, in the order its page tree lists them.
`/Kids` is followed one level of nesting deep — the writer emits a flat
tree, and a deeper one would show up as a missing page rather than a
silently wrong order. -/
private def artPageDicts (es : Array Entry) (trailer : Obj) : Array Obj := Id.run do
  let deref := PdfCensus.deref es
  let root := deref (((PdfCensus.catalogOf es trailer).get? "Pages").getD .null)
  let mut out : Array Obj := #[]
  let .arr kids := deref ((root.get? "Kids").getD .null) | return out
  for k in kids do
    let d := deref k
    if PdfCensus.kindOf d == .pages then
      if let .arr inner := deref ((d.get? "Kids").getD .null) then
        for j in inner do out := out.push (deref j)
    else out := out.push d
  return out

/-- A produced file read as pages of ink: the cross-reference followed by
the engine's own reader, each page's faces built from its own resources,
each page's content stream decoded and evaluated. A file the reader
refuses is a named error, never an empty reading. -/
def readArtifact (pdf : ByteArray) : Except String (Array ArtPage) := do
  let es ← PdfRead.objects pdf
  let trailer ← PdfRead.trailer pdf
  let esv := es.val
  let deref := PdfCensus.deref esv
  let mut out : Array ArtPage := #[]
  for page in artPageDicts esv trailer do
    let mut fonts : Std.HashMap String ArtFont := {}
    let resources := deref ((page.get? "Resources").getD .null)
    if let .dict fs := deref ((resources.get? "Font").getD .null) then
      for (nm, v) in fs do fonts := fonts.insert nm (artFontOf esv (deref v))
    let content ← match page.get? "Contents" with
      | some (.ref n _) =>
        match esv.find? (·.num == n) with
        | some e =>
          match e.decoded with
          | .ok (some data) => pure data
          | .ok none => throw "page content stream: not a stream"
          | .error err => throw s!"page content stream: {err}"
        | none => throw s!"page /Contents names object {n}, which the cross-reference does not list"
      | _ => throw "page has no /Contents reference"
    let (runs, boxes) := evalContent fonts (scanContent content)
    out := out.push { media := artRect ((page.get? "MediaBox").getD .null)
                      runs, boxes, content }
  return out


/-- The bytes the *driver* writes, not a reduced variant: the structure
tree the layout attributed against, the typed operators built from it, and
`Pdf.write` given both. `Pdf.write`'s `tree` argument defaults to the
empty tree, and a file written that way carries no structure elements and
marks every line `/Artifact` — so a tier that read it could not tell body
ink from running furniture, and would be judging a file no build ships.
This is the one spelling every artifact claim reads. -/
def driverPdf (fs : Font.FontSet) (geom : Layout.Geom) (doc : Ir.Doc)
    (out : Layout.Out) (store : Image.Store := {}) : ByteArray :=
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let ops := Pdf.pageOps geom fs out.pages store tree
  Pdf.write geom fs out.pages doc.info store out.outline #[] tree ops

/-- A rectangle in PDF user space, as the region vocabulary the claims
read: `x0 ≤ x1` and `y0 ≤ y1`. -/
structure ArtRect where
  x0 : Dim.Sp
  y0 : Dim.Sp
  x1 : Dim.Sp
  y1 : Dim.Sp
  deriving Repr, Inhabited

def ArtRect.render (r : ArtRect) : String :=
  s!"[{r.x0.toPtString} {r.y0.toPtString} {r.x1.toPtString} {r.y1.toPtString}]"

/-- Does the box `(bx0, by0, bx1, by1)` lie inside `r`, allowing `hslack`
left and right and `vslack` above and below? The two are separate because
the slack a text-area claim must allow is horizontal: character protrusion
hangs a boundary glyph into the margin by design, and nothing hangs a
baseline out of the measure. A vertical slack of a glyph's width would
excuse half a line of ink in a furniture band. -/
def ArtRect.holds (r : ArtRect) (hslack vslack bx0 by0 bx1 by1 : Dim.Sp) : Bool :=
  r.x0 - hslack ≤ bx0 && r.y0 - vslack ≤ by0 && bx1 ≤ r.x1 + hslack && by1 ≤ r.y1 + vslack

/-- Do two rectangles share area? Touching edges do not count: a band's
bottom edge and a body line's top edge may coincide. -/
def ArtRect.overlaps (a b : ArtRect) : Bool :=
  a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1

/-- The page's own declared medium, read from `/MediaBox`. The one region
in these claims that is a fact of the file rather than of the
document's declaration. -/
def ArtPage.box (p : ArtPage) : ArtRect :=
  { x0 := p.media.1, y0 := p.media.2.1, x1 := p.media.2.2.1, y1 := p.media.2.2.2 }

/-- The body area a geometry declares, in PDF user space: the measure
between the horizontal margins, and between `bodyTop` and `bodyBottom`
(which is where the engine's own placement decisions read the page's
vertical limits from). Derived from the document's declaration — an input
to the build — never from what the layout recorded. A deck whose chrome
footer draws has beamer's frame instead (`footline`): its text area runs
from the paper's top edge (moloch's headline is empty) to 4 pt above the
footline's ink, which the template declares to stand at least its closing
skip above the paper's edge — so the bound is `raise + sep`, the floor of a
band holding no ink (`Layout.footFloor_exact`). -/
def artBodyArea (geom : Layout.Geom) (footline : Bool := false) : ArtRect :=
  { x0 := geom.bleed + geom.hmargin
    y0 := geom.bleed + (if footline then Ir.footline.raise + Ir.footline.sep
      else geom.pageH - geom.bodyBottom)
    x1 := geom.bleed + geom.pageW - geom.hmargin
    y1 := geom.bleed + geom.pageH - (if footline then 0 else geom.bodyTop) }

/-- The least share of the page width a fill must span to read as a
furniture band rather than as a rule, a marker or a node's ground. Nine
tenths: the bands the engine paints (a frame's title bar, a poster's
headline, a chrome footer's ground) run the full trim width, and the
widest non-band fill in the corpus is a heading's underline. -/
def artBandWidthShare : Nat := 9

/-- The most a band may be of the page height. A band is a strip; a fill
spanning the whole page is the page's ground, which every themed deck
paints and which holds all of its ink by design — reading that as a band
would make the band claim vacuous on exactly the documents it is for. One
third: the tallest band the corpus paints is a poster's headline at a
fifth of the page. -/
def artBandHeightShare : Nat := 3

/-- The structure types a furniture band legitimately holds: the title a
frame's own band carries, and the headings a poster's headline band does.
Body prose, a table cell, a formula, a figure's label — none of these
belong in a band, and the eight-node picture that once collapsed into a
frame's title band carried `/Figure`. -/
def artBandTags : List String := ["Title", "H1", "H2", "H3", "H4", "H5", "H6"]

/-- The furniture bands a page paints, read from the file: a fill running
(almost) the whole medium, touching its top or bottom edge, and no taller
than `artBandHeightShare` of the page. The engine paints these as
`/Artifact` sequences, and a band is the one region where ink outside the
body area is the design rather than a defect — so the region a text-area
claim must allow is read from the bytes that painted it, not from a layout
record of the decision to paint it. -/
def ArtPage.bands (p : ArtPage) : Array ArtRect :=
  let box := p.box
  let wide := (box.x1 - box.x0) * artBandWidthShare / 10
  let short := (box.y1 - box.y0) / artBandHeightShare
  p.boxes.filterMap fun b =>
    if b.kind == "fill" && b.isArtifact && wide ≤ b.x1 - b.x0 && b.y1 - b.y0 ≤ short
        && (b.y1 ≥ box.y1 || b.y0 ≤ box.y0) then
      some { x0 := b.x0, y0 := b.y0, x1 := b.x1, y1 := b.y1 }
    else none

/-- The characters no page may paint as glyph ink. `inkMarkupWatch`'s
artifact twin, and deliberately the same three: a backslash or a brace is
the unambiguous signature of a page showing its source. -/
def artMarkupWatch : List Char := ['\\', '{', '}']


/-- The structure type a piece of content ink sits under, innermost
first: what a claim reads to tell a frame's own title from body prose
that has wandered into its band. Empty for artifact ink. -/
def ArtMark.tag? : ArtMark → Option String
  | .artifact _ => none
  | .content t _ => some t

def artInnerTag (marks : Array ArtMark) : Option String :=
  (marks.reverse.findSome? ArtMark.tag?)

/-- The precision at which the artifact can express a coordinate at all:
one hundredth of a point, comfortably above the writer's thousandth-of-a-
point spelling (`Sp.toPtString`) and the two roundings a box's far edge
accumulates when width and origin are spelled separately — a page-wide
fill's `x + w` misses the `/MediaBox` edge by a few millipoints every
time. Far below any defect this tier is for: the node label that shipped
at negative page x was 6.6 pt out. -/
def artSpellSlack : Dim.Sp := Dim.pt 1 / 100

/-- The one artifact claim this tier makes, per shape. Written as a
vocabulary so a recorded offence names the property it breaks and cannot
silently move to another. -/
inductive ArtProp where
  /-- Every mark the file paints lies inside the page's own `/MediaBox`. -/
  | pageBox
  /-- Every content-marked mark lies inside the declared body area, a
  painted band, or is accounted for by a named loss. -/
  | bodyArea
  /-- No body content — prose, a cell, a formula, a figure's ink — stands
  outside the text area and inside a painted furniture band. The guard on
  `bodyArea`'s band escape: without it, that escape would excuse exactly
  the eight-node picture that once collapsed into a frame's title band. -/
  | bandFree
  /-- No glyph the file paints decodes to a markup character. -/
  | markupInk
  /-- No two consecutive pages carry identical content streams. -/
  | pageBytes
  /-- Every CID the file shows is named by its own `/ToUnicode`. -/
  | glyphNames
  deriving BEq, Repr, Inhabited

def ArtProp.name : ArtProp → String
  | .pageBox => "ink inside the page box"
  | .bodyArea => "content ink inside the text area"
  | .bandFree => "no body ink outside the text area in a furniture band"
  | .markupInk => "no markup character as ink"
  | .pageBytes => "no two consecutive pages identical"
  | .glyphNames => "every shown glyph is named"

def artProps : List ArtProp :=
  [.pageBox, .bodyArea, .bandFree, .markupInk, .pageBytes, .glyphNames]

/-- The diagnostic codes whose declared meaning accounts for ink that did
not fit where it was asked to go: `W0005` (overfull line, no feasible
break), `W0335` (picture larger than the text area; it may overrun the
page), and `W0388` (ink painted off the medium, which a viewer clips). A
document that ships ink outside its own area and says one of these has
reported the loss; one that says nothing has not.

`W0388` is the page box's own account, and it arrived with this tier: a
band slot sets one line at a fixed position and at a width it does not
control, so a token with no legal break reached 140 pt past the right page
edge and no registered code said so. That was the offence recorded here
until the code existed. -/
def artOverflowCodes : List String := ["W0005", "W0335", "W0388"]

/-- A fixture's reading, with the two facts a claim needs beside it: the
body area the document declared, and whether its build named a loss that
accounts for ink outside it. -/
structure ArtReading where
  pages : Array ArtPage
  area : ArtRect
  accounted : Bool
  deriving Inhabited

/-- Every way a reading breaks one claim, each named with the page, the
box, and the ink. Both the gate and the offence ratchet read this one
function, so a recorded offence cannot be recorded against a judgement
nothing computes. -/
def artOffences (r : ArtReading) : ArtProp → Array String
  | .pageBox => Id.run do
    let mut out : Array String := #[]
    for h : i in [0:r.pages.size] do
      let p := r.pages[i]
      let box := p.box
      for run in p.runs do
        unless box.holds artSpellSlack artSpellSlack run.x run.bottom run.x1 run.top || r.accounted do
          out := out.push s!"p{i + 1} glyph run [{run.x.toPtString} {run.bottom.toPtString} \
{run.x1.toPtString} {run.top.toPtString}] outside {box.render}: {run.text}"
      for b in p.boxes do
        unless box.holds artSpellSlack artSpellSlack b.x0 b.y0 b.x1 b.y1 || r.accounted do
          out := out.push s!"p{i + 1} {b.kind} [{b.x0.toPtString} {b.y0.toPtString} \
{b.x1.toPtString} {b.y1.toPtString}] outside {box.render}"
    return out
  | .bodyArea => Id.run do
    let mut out : Array String := #[]
    if r.accounted then return out
    for h : i in [0:r.pages.size] do
      let p := r.pages[i]
      let bands := p.bands
      for run in p.runs do
        unless run.isArtifact do
          let rect : ArtRect := { x0 := run.x, y0 := run.bottom, x1 := run.x1, y1 := run.inkTop }
          unless r.area.holds run.widest artSpellSlack run.x run.bottom run.x1 run.inkTop
              || bands.any (·.overlaps rect) do
            out := out.push s!"p{i + 1} glyph run {rect.render} outside \
{r.area.render}: {run.text}"
      for b in p.boxes do
        unless b.isArtifact do
          let rect : ArtRect := { x0 := b.x0, y0 := b.y0, x1 := b.x1, y1 := b.y1 }
          unless r.area.holds artSpellSlack artSpellSlack b.x0 b.y0 b.x1 b.y1 || bands.any (·.overlaps rect) do
            out := out.push s!"p{i + 1} {b.kind} {rect.render} outside {r.area.render}"
    return out
  | .bandFree => Id.run do
    let mut out : Array String := #[]
    for h : i in [0:r.pages.size] do
      let p := r.pages[i]
      let bands := p.bands
      if bands.isEmpty then continue
      for run in p.runs do
        let tag := artInnerTag run.marks
        unless tag.isNone || (tag.map artBandTags.contains).getD false do
          let rect : ArtRect := { x0 := run.x, y0 := run.bottom, x1 := run.x1, y1 := run.inkTop }
          unless r.area.holds run.widest artSpellSlack run.x run.bottom run.x1 run.inkTop do
            if bands.any (·.overlaps rect) then
              out := out.push s!"p{i + 1} /{tag.getD ""} run {rect.render} stands outside \
{r.area.render} and inside a band: {run.text}"
      for b in p.boxes do
        unless b.isArtifact do
          let rect : ArtRect := { x0 := b.x0, y0 := b.y0, x1 := b.x1, y1 := b.y1 }
          unless r.area.holds artSpellSlack artSpellSlack b.x0 b.y0 b.x1 b.y1 do
            if bands.any (·.overlaps rect) then
              out := out.push s!"p{i + 1} {b.kind} {rect.render} stands outside \
{r.area.render} and inside a band"
    return out
  | .markupInk => Id.run do
    let mut out : Array String := #[]
    for h : i in [0:r.pages.size] do
      for run in r.pages[i].runs do
        for c in artMarkupWatch do
          if run.text.any (· == c) then
            out := out.push s!"p{i + 1} ships '{c}' as ink: {run.text}"
    return out
  | .pageBytes => Id.run do
    let mut out : Array String := #[]
    for h : i in [1:r.pages.size] do
      if r.pages[i - 1]!.content.data == r.pages[i].content.data then
        out := out.push s!"p{i} and p{i + 1} carry identical content streams \
({r.pages[i].content.size} bytes)"
    return out
  | .glyphNames => Id.run do
    let mut out : Array String := #[]
    let repl := Char.ofNat 0xFFFD
    for h : i in [0:r.pages.size] do
      for run in r.pages[i].runs do
        if run.text.any (· == repl) then
          out := out.push s!"p{i + 1} shows a glyph its /ToUnicode does not name: {run.text}"
    return out

/-- The artifact offences the corpus ships today: the fixture, the claim
it breaks, and what the engine does wrong. These are not permissions —
they are routed defects, recorded so the claim stays armed on the other
seventy-odd fixtures instead of being weakened for these. The ratchet:
`artifactChecks` fails a row whose offence has stopped firing, so the
table can only shrink, and a fix must delete its row in the same commit. -/
def artKnownOffences : List (String × ArtProp × String) := []


/-! ## The mutants: each claim broken once, on real bytes

A gate that does not catch the shape it commemorates grants false
confidence, so every claim above is shown failing on a produced PDF whose
ink was moved. The mutation is applied to the writer's own typed
operators, which `Pdf.write` accepts as an argument — so the mutant is a
whole file written by the real writer, cross-reference, fonts and
`/ToUnicode` included, differing from the fixture only in where the ink
went. That is the defect shape: the layout's record says one thing, the
painted page another, and this tier reads the page. -/

def artTagIsArtifact : Pdf.MarkTag → Bool
  | .artifact _ => true
  | .content _ _ _ => false

mutual

/-- Every `Tm` inside a text object displaced, optionally only inside
content sequences (leaving running furniture where it was). -/
def artMoveTextOp (onlyContent : Bool) (dx dy : Dim.Sp) : Pdf.TextOp → Pdf.TextOp
  | .move x y => .move (x + dx) (y + dy)
  | .marked t body =>
    if onlyContent && artTagIsArtifact t then .marked t body
    else .marked t (artMoveTextList onlyContent dx dy #[] body.toList)
  | o@(.scale _) => o
  | o@(.font _ _) => o
  | o@(.color _) => o
  | o@(.show _) => o

def artMoveTextList (onlyContent : Bool) (dx dy : Dim.Sp) (acc : Array Pdf.TextOp) :
    List Pdf.TextOp → Array Pdf.TextOp
  | [] => acc
  | o :: rest => artMoveTextList onlyContent dx dy (acc.push (artMoveTextOp onlyContent dx dy o)) rest

end

mutual

/-- One page's operators with its text displaced. Fills and paths stay
where they were, so a band keeps its place while the ink moves. -/
def artMoveOp (onlyContent : Bool) (dx dy : Dim.Sp) : Pdf.ContentOp → Pdf.ContentOp
  | .text ops => .text (artMoveTextList onlyContent dx dy #[] ops.toList)
  | .marked t body => .marked t (artMoveList onlyContent dx dy #[] body.toList)
  | o@(.fill _ _ _ _ _) => o
  | o@(.path _ _ _) => o
  | o@(.image _ _ _ _ _) => o
  | o@(.imageMissing _ _ _ _) => o

def artMoveList (onlyContent : Bool) (dx dy : Dim.Sp) (acc : Array Pdf.ContentOp) :
    List Pdf.ContentOp → Array Pdf.ContentOp
  | [] => acc
  | o :: rest => artMoveList onlyContent dx dy (acc.push (artMoveOp onlyContent dx dy o)) rest

end

mutual

/-- The first glyph of every run replaced by `gid`: a glyph the file's own
`/ToUnicode` never names, because the CMap is built from the pages the
layout produced and this identifier is not among them. -/
def artRegidTextOp (gid : Nat) : Pdf.TextOp → Pdf.TextOp
  | .show items => .show (items.map fun it => match it with
      | .glyphs gs => .glyphs (if gs.isEmpty then gs else gs.set! 0 gid)
      | .kerned gs ns => .kerned (if gs.isEmpty then gs else gs.set! 0 gid) ns
      | a@(.adjust _) => a)
  | .marked t body => .marked t (artRegidTextList gid #[] body.toList)
  | o@(.scale _) => o
  | o@(.move _ _) => o
  | o@(.font _ _) => o
  | o@(.color _) => o

def artRegidTextList (gid : Nat) (acc : Array Pdf.TextOp) :
    List Pdf.TextOp → Array Pdf.TextOp
  | [] => acc
  | o :: rest => artRegidTextList gid (acc.push (artRegidTextOp gid o)) rest

end

mutual

def artRegidOp (gid : Nat) : Pdf.ContentOp → Pdf.ContentOp
  | .text ops => .text (artRegidTextList gid #[] ops.toList)
  | .marked t body => .marked t (artRegidList gid #[] body.toList)
  | o@(.fill _ _ _ _ _) => o
  | o@(.path _ _ _) => o
  | o@(.image _ _ _ _ _) => o
  | o@(.imageMissing _ _ _ _) => o

def artRegidList (gid : Nat) (acc : Array Pdf.ContentOp) :
    List Pdf.ContentOp → Array Pdf.ContentOp
  | [] => acc
  | o :: rest => artRegidList gid (acc.push (artRegidOp gid o)) rest

end

/-- A file written from the fixture's own inputs with one page's operators
replaced. The writer, the fonts, the structure tree and the cross-
reference are the real ones. -/
def artWriteWith (fs : Font.FontSet) (geom : Layout.Geom) (doc : Ir.Doc)
    (out : Layout.Out) (store : Image.Store)
    (f : Array (Array Pdf.ContentOp) → Array (Array Pdf.ContentOp)) : ByteArray :=
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let ops := Pdf.pageOps geom fs out.pages store tree
  Pdf.write geom fs out.pages doc.info store out.outline #[] tree (f ops)

/-- Page `i`'s operators rewritten, the rest untouched. -/
def artOnPage (i : Nat) (g : Array Pdf.ContentOp → Array Pdf.ContentOp)
    (ops : Array (Array Pdf.ContentOp)) : Array (Array Pdf.ContentOp) :=
  if h : i < ops.size then ops.set i (g ops[i]) else ops

/-- Page `j`'s operators replaced by page `i`'s: the overlay increment
that vanished, which left two deck pages byte-identical while the page
count still matched its reference. -/
def artCopyPage (i j : Nat) (ops : Array (Array Pdf.ContentOp)) :
    Array (Array Pdf.ContentOp) :=
  match ops[i]? with
  | some src => if j < ops.size then ops.set! j src else ops
  | none => ops


/-- A file read as a reading, with the declared area and whether the build
named a loss that accounts for ink outside it. -/
def artReadingOf (geom : Layout.Geom) (accounted : Bool) (pdf : ByteArray)
    (footline : Bool := false) :
    Except String ArtReading :=
  (readArtifact pdf).map fun pages =>
    { pages := pages, area := artBodyArea geom footline, accounted := accounted }

/-- Did this build name a loss that accounts for ink outside the declared
area? Read from the whole build's diagnostics — elaboration and layout
alike, since a picture that will overrun is a layout finding. -/
def artAccounted (diags : Array Diag) : Bool :=
  diags.any fun d => artOverflowCodes.contains d.code

/-- Where the layout put each glyph of a page, in PDF user space and in
stream order: the line's x, the segments before it, and the glyph's laid
advance from its run's start under the line's expansion, by the rule
`Layout.setLine` scales a run by (`w + w·f/1000`). -/
def artLaidGlyphs (geom : Layout.Geom) (p : Layout.PageOut) : Array Dim.Sp := Id.run do
  let mut out : Array Dim.Sp := #[]
  for l in p.lines do
    let mut x := geom.bleed + l.x
    for s in l.segs do
      match s with
      | .run _ _ _ w glyphs _ _ _ _ _ _ =>
        let mut adv : Dim.Sp := 0
        for (_, _, a) in glyphs do
          out := out.push (x + adv + adv * l.expand / 1000)
          adv := adv + a
        x := x + w
      | .gap w _ | .decoratedGap w _ _ => x := x + w
      | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
      | .image _ w _ => x := x + w
      | .poly _ _ => pure ()
  return out

/-- Glyphs whose painted start misses the layout's: the file's pen, glyph
by glyph — each with the size its run is set at — against `artLaidGlyphs`,
beyond what the file can state: half a thousandth of that size (a `TJ`
number's resolution, `Pdf.place_between`'s bound) plus the precision a
coordinate is spelled at (`artSpellSlack`). A count that differs is an
offence of its own. -/
def artGlyphPlacementOffences (laid : Array Dim.Sp) (painted : Array (Dim.Sp × Dim.Sp)) :
    Array String := Id.run do
  if laid.size != painted.size then
    return #[s!"{painted.size} glyphs painted where the layout placed {laid.size}"]
  let mut out : Array String := #[]
  for h : k in [0:laid.size] do
    let (x, size) := painted[k]!
    let d := x - laid[k]
    if d.natAbs > (artSpellSlack + size / 2000).natAbs then
      out := out.push s!"glyph {k}: painted {(d : Dim.Sp).toPtString}pt from its layout x"
  return out

/-- A page's painted glyph starts, in stream order, each with its run's size. -/
def artPaintedGlyphs (p : ArtPage) : Array (Dim.Sp × Dim.Sp) :=
  p.runs.flatMap fun r => r.glyphs.map fun (x, _) => (x, r.size)

/-- A font name without its subset tag, the six capitals and a plus a
subset's name opens with (ISO 32000-2 §9.6.4). -/
def artBaseName (n : String) : String :=
  let cs := n.toList
  if cs.length > 7 && cs[6]? == some '+' && (cs.take 6).all Char.isUpper then
    String.ofList (cs.drop 7)
  else n

/-- Each face the pages' own resources name, as the file states it: its
descriptor's `/FontName`, the program its `FontFile2`/`FontFile3` stream
carries, and every glyph id the pages' text operators paint in it
(`Identity-H` spells a glyph in two bytes). A placed PDF figure's fonts
live in its form's resources and are the figure's, not the engine's. -/
def artEmbedded (pdf : ByteArray) :
    Except String (Array (String × ByteArray × Array Nat)) := do
  let es := (← PdfRead.objects pdf).val
  let deref := PdfCensus.deref es
  let mut faces : Std.HashMap Nat String := {}
  let mut painted : Std.HashMap Nat (Array Nat) := {}
  for e in es do
    unless e.val.get? "Type" == some (.name "Page") do continue
    let res := deref ((e.val.get? "Resources").getD .null)
    let mut names : Std.HashMap String Nat := {}
    if let .dict fs := deref ((res.get? "Font").getD .null) then
      for (nm, v) in fs do
        let cid := match deref ((deref v).get? "DescendantFonts" |>.getD .null) with
          | .arr xs => deref (xs[0]?.getD .null)
          | d => d
        let fd := deref ((cid.get? "FontDescriptor").getD .null)
        let some (.name fn) := fd.get? "FontName" | throw s!"{nm}: its descriptor has no name"
        let some (.ref pn _) := (fd.get? "FontFile2").orElse fun _ => fd.get? "FontFile3"
          | throw s!"{fn}: no embedded program"
        names := names.insert nm pn
        faces := faces.insert pn fn
    let some (.ref cn _) := e.val.get? "Contents" | throw "a page has no /Contents reference"
    let some c := es.find? (·.num == cn) | throw "a page's /Contents names no object"
    let .ok (some data) := c.decoded | throw "a page content stream does not decode"
    let mut cur : Option Nat := none
    let mut stack : Array CTok := #[]
    for tok in scanContent data do
      match tok with
      | .op o =>
        if o == "Tf" then
          cur := (stack.findSome? fun | .name n => some n | _ => none).bind names.get?
        else if o == "TJ" || o == "Tj" then
          if let some pn := cur then
            for s in stack do
              if let .hex d := s then painted := painted.insert pn (painted.getD pn #[] ++ artCodes d)
        stack := #[]
      | t => stack := stack.push t
  let mut out : Array (String × ByteArray × Array Nat) := #[]
  for (pn, fn) in faces.toArray.qsort (fun a b => a.1 < b.1) do
    let some pe := es.find? (·.num == pn) | throw s!"{fn}: its program names no object"
    let .ok (some bytes) := pe.decoded | throw s!"{fn}: its program does not decode"
    out := out.push (fn, bytes, painted.getD pn #[])
  return out

/-- The artifact tier over the golden corpus: every fixture built the way
the driver builds it, its bytes read back, and every claim judged on what
they paint. A recorded offence inverts the judgement — the row must still
fire — so a fix that removes an offence fails until its row goes too. -/
def artifactCorpusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  for (n, p, _) in artKnownOffences do
    t s!"artifact offence row {n}/{p.name}: names a golden fixture" (goldenNames.contains n)
  t "artifact offence rows are distinct"
    (artKnownOffences.length ==
      (artKnownOffences.map fun (n, p, _) => s!"{n}/{p.name}").eraseDups.length)
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut bandsSeen := 0
  let mut multiPage := 0
  let mut contentPaths := 0
  let mut subsets := 0
  for n in goldenNames do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, diags) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc
    let out := layoutOf fs doc geom (some pats) store
    let pdf := driverPdf fs geom doc out store
    let footline := doc.docClass.record.chrome && doc.foot.isNone &&
      (doc.chrome.hasFooter || doc.body.any fun b => match b with
        | .framefoot xs => !xs.isEmpty
        | _ => false)
    match artReadingOf geom (artAccounted (diags ++ out.diags)) pdf footline with
    | .error e => t s!"artifact {n}: the file reads back: {e}" false
    | .ok rd =>
      t s!"artifact {n}: the file's page count is the layout's \
({rd.pages.size} vs {out.pages.size})" (rd.pages.size == out.pages.size)
      if 1 < rd.pages.size then multiPage := multiPage + 1
      for p in rd.pages do
        bandsSeen := bandsSeen + p.bands.size
        contentPaths := contentPaths + (p.boxes.filter fun b => !b.isArtifact).size
      let placed := artGlyphPlacementOffences (out.pages.flatMap (artLaidGlyphs geom))
        (rd.pages.flatMap artPaintedGlyphs)
      t s!"artifact {n}: every glyph starts where the layout put it: {placed.toList.take 3}"
        placed.isEmpty
      -- The embedded programs: every glyph the pages paint is drawn as the
      -- face draws it, and a program named a subset is one.
      match artEmbedded pdf with
      | .error e => t s!"artifact {n}: its fonts read back: {e}" false
      | .ok faces =>
        for (fn, prog, gids) in faces do
          match fs.fonts.find? (·.psName == artBaseName fn) with
          | none => t s!"artifact {n}: {fn} names a face of the set" false
          | some f =>
            let src := Ink.Src.make f.data f.isCff f.numGlyphs
            let emb := Ink.Src.make prog f.isCff f.numGlyphs
            let lost := gids.filter fun g => emb.cmdsAt g != src.cmdsAt g
            t s!"artifact {n}: {fn} draws every glyph the pages paint as its face does: \
{lost.toList.take 5}" lost.isEmpty
            if artBaseName fn != fn then
              subsets := subsets + 1
              let dropped := (List.range f.numGlyphs).any fun g =>
                g != 0 && !gids.contains g && emb.cmdsAt g == some #[] && src.cmdsAt g != some #[]
              t s!"artifact {n}: {fn} is named a subset and is one"
                (prog.size < f.data.size && dropped)
            else
              let spared := (List.range f.numGlyphs).filter fun g =>
                g != 0 && !gids.contains g && src.cmdsAt g != some #[]
              t s!"artifact {n}: {fn} embeds whole only when its pages paint every glyph \
it draws: {spared.take 5}" spared.isEmpty
      for prop in artProps do
        let offs := artOffences rd prop
        if artKnownOffences.any fun (f, q, _) => f == n && q == prop then
          t s!"artifact {n}: the recorded offence against {prop.name} no longer \
fires — delete its row from artKnownOffences" (!offs.isEmpty)
        else
          t s!"artifact {n}: {prop.name}: {offs.toList}" offs.isEmpty
  -- Non-vacuity: a claim about a region no fixture paints proves nothing.
  t s!"artifact corpus: furniture bands are reached ({bandsSeen})" (0 < bandsSeen)
  t s!"artifact corpus: multi-page fixtures are read ({multiPage})" (1 < multiPage)
  t s!"artifact corpus: content paths and images are reached ({contentPaths})" (0 < contentPaths)
  t s!"artifact corpus: embedded faces are subsets ({subsets})" (0 < subsets)

/-- Each claim broken once, on a file the real writer produced, and each
one's untouched control passing. The mutation moves ink or re-identifies a
glyph in the writer's own typed operators; nothing else about the file
changes, so a claim that stays silent here is a claim that would have
stayed silent on the defect it commemorates. -/
def artifactMutantChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let build (n : String) :
      IO (Font.FontSet × Layout.Geom × Ir.Doc × Layout.Out × Image.Store) := do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc
    return (fs, geom, doc, layoutOf fs doc geom (some pats) store, store)
  let judge (label : String) (prop : ArtProp) (geom : Layout.Geom) (pdf : ByteArray)
      (wantOffence : Bool) : IO Unit :=
    match artReadingOf geom false pdf with
    | .error e => t s!"artifact mutant {label}: reads back: {e}" false
    | .ok rd =>
      let offs := artOffences rd prop
      if wantOffence then
        t s!"artifact mutant {label}: {prop.name} refuses it" (!offs.isEmpty)
      else
        t s!"artifact mutant {label}: the control passes {prop.name}: {offs.toList}" offs.isEmpty
  let (fs, geom, doc, out, store) ← build "paragraphs"
  let plain := driverPdf fs geom doc out store
  let moved (onlyContent : Bool) (dx dy : Dim.Sp) (page : Nat)
      (f : Font.FontSet) (g : Layout.Geom) (d : Ir.Doc) (o : Layout.Out)
      (s : Image.Store) : ByteArray :=
    artWriteWith f g d o s (artOnPage page (artMoveList onlyContent dx dy #[] ·.toList))
  judge "every Tm 200pt left of the page" .pageBox geom
    (moved false (-(Dim.pt 200)) 0 0 fs geom doc out store) true
  judge "paragraphs untouched" .pageBox geom plain false
  judge "content Tm 30pt into the margin" .bodyArea geom
    (moved true (-(Dim.pt 30)) 0 0 fs geom doc out store) true
  judge "paragraphs untouched" .bodyArea geom plain false
  judge "a glyph the /ToUnicode does not name" .glyphNames geom
    (artWriteWith fs geom doc out store (artOnPage 0 (artRegidList 60000 #[] ·.toList))) true
  judge "paragraphs untouched" .glyphNames geom plain false
  -- The band claim needs a page that paints one: chrome's third frame. The
  -- lift is read off the layout, never fitted to today's geometry: the
  -- frame's body line lands with its baseline in the middle of the page's
  -- title band, wherever the body opens (review F8: a fitted 110pt stopped
  -- lifting the line into the band the day the body moved down).
  let (cf, cg, cd, co, cs) ← build "chrome"
  let lift : Dim.Sp := ((co.pages[2]?).bind fun p => p.band.bind fun band =>
    (p.lines.find? fun l => !l.furniture && l.y > band).map fun l => l.y - band / 2).getD 0
  t "artifact mutant: the chrome fixture's third frame has a band and a body line below it"
    (0 < lift)
  judge "body prose lifted into the middle of a title band" .bandFree cg
    (moved true 0 lift 2 cf cg cd co cs) true
  judge "chrome untouched" .bandFree cg (driverPdf cf cg cd co cs) false
  -- The vanished overlay increment: two consecutive pages, one content stream.
  let (of_, og, od, oo, os) ← build "overlays"
  judge "an overlay step's page replaced by the previous one" .pageBytes og
    (artWriteWith of_ og od oo os (artCopyPage 0 1)) true
  judge "overlays untouched" .pageBytes og (driverPdf of_ og od oo os) false
  -- Markup as ink: the check judges the character, not its provenance
  -- (as `inkMarkupChecks` does, exemption table and all), so an authored
  -- backslash is its witness — a `\verb` run's code is one. The corpus
  -- ships none; the recovery path that could leak one (an unmodelled
  -- command's argument) is checked silent beside it.
  for (label, src, want) in [
      ("an authored backslash", dvDoc "" "a \\textbackslash{} b", true),
      ("authored braces", dvDoc "" "a \\{x\\} b", true),
      ("a verbatim run's own code", dvDoc "" "\\verb|\\foo{bar}|", true),
      ("an unmodelled command's argument", dvDoc "" "\\parbox{.25\\textwidth}{x}", false)] do
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let o := layoutOf oneFace d g (some pats)
    judge s!"markup ink: {label}" .markupInk g (driverPdf oneFace g d o) want

def artifactChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  artifactMutantChecks ref oneFace pats
  artifactCorpusChecks ref oneFace pats


/-! ## Backend parity: the furniture band both artifacts carry

**The invariant.** A furniture band's *existence* is a fact of the
document, not of an artifact. One palette key declares it — `frametitlebg`,
a declared consumed role (`Ir.Design.consumedRoles`, which names both
consumers) — and `Ir.Design.frametitle` is the resolved value each backend
reads. Each then carries the band its own way: the PDF paints a full-width
artifact fill against the page's top edge, the HTML declares a rule
painting an element's background from the band's custom property. So the
claim is that the two agree about existence, and it is checked as the chain
the one declaration forms:

    a painted band ⟹ the design declares the pair ⟹ the HTML carries it

with the last link's converse — no rule without the declaration — closing
the loop. Composed that is parity; separated, each link is a claim with its
own witness, so a break names which end lost the band rather than only that
the two differ.

**The direction that is not claimed.** `declares ⟹ paints` is false, and
deliberately absent: the PDF resolves the band per frame against the
palette epoch in force (`Layout.collectFrameTitle` reads `a.pal`), while
the HTML emits one document-level rule from `Ir.Design.ofDoc doc`. A
document that declares the pair and titles no frame paints nothing, and is
correct. Asserting the converse would pass on today's corpus — every
declaring fixture happens to title a frame — and fire falsely on the first
legitimate one that does not, which is the failure mode this block was
repaired for.

**Why not a class name.** This block used to search the emitted HTML for
eight guessed class names (`slide-title`, `titlebar`, …), none of which this
backend has ever emitted: the band is `section.slide > header`, carrying no
class at all, painted by a rule that was present, read, and visible on a
raster the whole time. It therefore recorded twenty offences that were all
false while staying green, which is worse than no gate — a ratchet of false
positives invites being lowered, and a gate that never detected the band
cannot fire when the band goes. The repair keys on the *declaration* (the
role, which the engine registers) instead of the *spelling* (a class, which
is the emitter's private choice), and resolves each painting rule's own
selector against the tree rather than guessing what the selector says.
Renaming the element and its rule together must keep this block green;
`artBandMutants` pins that, beside the four ways the band can genuinely go.

**Why not `htmlTokenClosureChecks`.** That block holds a declared token
against *some* rule referencing it, over the corpus union — it cannot see
which document, which element, or whether the element exists.
`frametitlebg` would stay read there if one poster kept its rule while
every deck lost its header. This block is per fixture, is joined to the
PDF's own bytes, and demands the carrier as well as the reference.

**Why a check and not a theorem.** The `_agree` form wants the two
backends' band to be two projections of one value, and it is one
factorization away. The PDF resolves the pair at `Layout.collectFrameTitle`
with its own default chain (`frametitlefg` → `bg` → white) — the same chain
`Ir.Design.ofDoc` applies, whose docstring claims to be the one
construction site. Factor that chain into a `Design.ofPalette` the frame
site calls with its epoch palette, and the statement becomes available in
`Ir.lean`: the pair the PDF resolves at a frame is
`(Design.ofPalette pal).frametitle`, so the band is one value both backends
project. Until then the two sides are functions of different values and
there is nothing to quantify over, so the joint is checkable only by
reading both artifacts, which is what this block does. -/

/-- The palette role that declares the band, and the custom property the
HTML backend names after it. Keyed on the role rather than on any class:
the role is what a document declares and the engine registers, while the
element is the emitter's choice and is resolved below. -/
def artBandRole : String := "frametitlebg"

/-- Does this declaration list paint a background from this role's property?
The property is read as a declaration — `background` or `background-color`
before the colon — so a `var()` reference in a border or a shadow does not
answer for the ground. Both reference forms count, bare and with a
fallback: the backend writes `var(--name, fallback)` as often as
`var(--name)`, and a scan for the bare closing paren alone is what once
reported a read token as unread (`Tests/HtmlTokens.lean` records it).

The role is the parameter because two grounds are judged by the same
three-link chain — the frame's furniture band and the title page's own
ground — and a second copy of this scan is how the two would drift. -/
def artPaintsFrom (role : String) (decls : String) : Bool :=
  (decls.splitOn ";").any fun d =>
    match d.splitOn ":" with
    | [] => false
    | prop :: rest =>
      let value := String.intercalate ":" rest
      (prop.trimAscii.toString == "background" ||
          prop.trimAscii.toString == "background-color") &&
        (hasStr value s!"var(--{role})" || hasStr value s!"var(--{role},")

def artPaintsBand (decls : String) : Bool := artPaintsFrom artBandRole decls

/-- An element as the tree carries it: its tag and its classes. -/
abbrev ArtElem := String × Array String

/-- One compound selector, and whether it must be a direct child of the
compound before it. A selector is an array of these, root first. -/
abbrev ArtStep := ArtElem × Bool

/-- One compound selector as the element it names: its tag (empty when the
compound is classes only) and every class it requires. Pseudo-classes and
pseudo-elements drop, because they constrain an element's state, not which
element it is. -/
def artCompound (tok : String) : Option ArtElem :=
  let bare := (tok.splitOn ":").headD tok
  let bits := (bare.splitOn ".").filter fun s => !s.isEmpty
  let tag := if bare.startsWith "." then "" else bits.headD ""
  let classes := (if bare.startsWith "." then bits else bits.drop 1).toArray
  if tag.isEmpty && classes.isEmpty then none else some (tag, classes)

/-- One selector as its chain of compounds, root first. Descendant and
child combinators only: a sibling combinator returns `none`, which the
judge reads as a selector it cannot resolve and *reports* — an unreadable
selector must never pass for a satisfied one. -/
def artSelChain (part : String) : Option (Array ArtStep) := Id.run do
  if part.any fun c => c == '+' || c == '~' then return none
  let toks := ((part.replace ">" " > ").splitOn " ").filter fun s => !s.isEmpty
  let mut steps : Array ArtStep := #[]
  let mut child := false
  for tok in toks.toArray do
    if tok == ">" then
      child := true
    else
      match artCompound tok with
      | none => return none
      | some e =>
        steps := steps.push (e, child)
        child := false
  if steps.isEmpty then return none else return some steps

/-- Every chain a selector list resolves to, one per comma-separated
selector this check can read. -/
def artSelChains (sel : String) : Array (Array ArtStep) :=
  ((sel.splitOn ",").filterMap artSelChain).toArray

/-- Does this element satisfy one compound? -/
def artCompMatches (c : ArtElem) (e : ArtElem) : Bool :=
  (c.1.isEmpty || e.1 == c.1) && c.2.all fun x => e.2.contains x

/-- Does a selector chain match this ancestor path, the path's last element
being the rule's subject? Matched right to left: the subject must be the
element itself, a child step must match the element immediately above, and
a descendant step may skip ancestors. Bounded by the path length, so total.

The ancestor chain is matched rather than the subject alone, which is what
makes a *moved* element a failure and not a pass: a header lifted out of
`section.slide` stops being painted, and a check that read only the subject
would report it carried. The walk is greedy, so a chain repeating one
compound under a child combinator could be reported unmatched when a match
exists — the error direction is over-strictness, which fails loudly, never
a silent pass. -/
def artChainMatchesPath (chain : Array ArtStep) (path : Array ArtElem) : Bool := Id.run do
  if chain.isEmpty || path.isEmpty then return false
  let subject := chain[chain.size - 1]!
  unless artCompMatches subject.1 path[path.size - 1]! do return false
  let mut ci := chain.size - 1
  let mut pi := path.size - 1
  let mut mustBeChild := subject.2
  for _ in [0:path.size + 1] do
    if ci == 0 then break
    if pi == 0 then return false
    let step := chain[ci - 1]!
    if artCompMatches step.1 path[pi - 1]! then
      ci := ci - 1
      pi := pi - 1
      mustBeChild := step.2
    else if mustBeChild then
      return false
    else
      pi := pi - 1
  return ci == 0

mutual

/-- Does this subtree ship an element the chain selects? The path threads
down the walk, so each element is judged against its own ancestors. The
tree is read for the carrier, never the printed page (AGENTS.md, the
page-claim rule). -/
def artChainInOne (chain : Array ArtStep) (path : Array ArtElem) : Html.Node → Bool
  | .text _ => false
  | .style _ => false
  | .script _ _ => false
  | .elem t attrs kids =>
    let cls := ((attrs.find? fun a => a.1 == "class").map (·.2)).getD ""
    let classes := ((cls.splitOn " ").filter fun s => !s.isEmpty).toArray
    let here := path.push (t, classes)
    artChainMatchesPath chain here || artChainInList chain here kids.toList

def artChainInList (chain : Array ArtStep) (path : Array ArtElem) :
    List Html.Node → Bool
  | [] => false
  | k :: rest => artChainInOne chain path k || artChainInList chain path rest

end

mutual

/-- Every stylesheet a typed tree carries, concatenated. `Html.Node.style`
is the one constructor that holds CSS, so the rules are read from the node
that will be printed rather than from a search of the rendered page. -/
def artTreeCssOne (acc : String) : Html.Node → String
  | .style css => acc ++ css
  | .text _ => acc
  | .script _ _ => acc
  | .elem _ _ kids => artTreeCssList acc kids.toList

def artTreeCssList (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => artTreeCssList (artTreeCssOne acc k) rest

end

/-- The ancestors `emitTree` does not return. Its two arrays are the
*children* of `head` and of `body`; `Html.document` builds those two
elements and the root around them. A selector anchored at `body` — the
poster's headline band is `body > header.headline` — resolves against
nothing unless the path it is matched along starts where the document
does. -/
def artBodyPath : Array ArtElem := #[("html", #[]), ("body", #[])]

/-- The selectors under which a stylesheet paints a background from a role. -/
def artGroundSelectors (role : String) (css : String) : Array String :=
  (artCssBlocks css).filterMap fun (sel, decls) =>
    if artPaintsFrom role decls then some sel else none

/-- The selectors under which a stylesheet paints the band. -/
def artBandSelectors (css : String) : Array String :=
  artGroundSelectors artBandRole css

/-- Every way a document's two artifacts disagree about its furniture band,
each named with the end that lost it: the three links of the chain and
nothing else. Whether the band *should* exist is the document's to say, and
this judge only holds the artifacts to what it declared.

Pure in its four arguments — the bytes' verdict, the design's, the emitted
stylesheet, the emitted body — so the same judgement that runs over the
corpus runs over the mutants. A judge reachable only through a 77-fixture
build is a judge whose failure nobody has seen. -/
def artBandOffences (painted declared : Bool) (css : String)
    (body : Array Html.Node) : Array String := Id.run do
  let mut out : Array String := #[]
  let sels := artBandSelectors css
  if painted && !declared then
    out := out.push s!"a page paints a top-edge furniture band while the design \
declares no band pair: --{artBandRole} is unset"
  if !sels.isEmpty && !declared then
    out := out.push s!"the stylesheet paints from --{artBandRole} with no band \
pair declared: {sels.toList}"
  if declared then
    if sels.isEmpty then
      out := out.push s!"the design declares a band pair and no rule paints a \
background from --{artBandRole}"
    else
      let readable := sels.filter fun s => !(artSelChains s).isEmpty
      if readable.isEmpty then
        out := out.push s!"no selector painting the band resolves to an element \
this check can read: {sels.toList}"
      else unless readable.any fun s =>
          (artSelChains s).any fun c => artChainInList c artBodyPath body.toList do
        out := out.push s!"every rule painting the band selects an element the \
tree does not ship: {readable.toList}"
  return out

/-- The golden fixtures whose two artifacts disagree about their furniture
band. Empty, and that is the repair: every one of the twenty rows this list
carried was false. Seven named a fixture whose PDF paints a band and whose
HTML already carried the rule and the element — the guessed class names were
the only thing missing. The other thirteen named fixtures that paint no band
at all, so the gate never reached their rows to contradict them: three decks
are unthemed (no `frametitlebg`, hence no band in either artifact, which is
agreement) and the rest are frame fixtures under no bundle.

A ratchet in both directions all the same: a row whose fixture starts
agreeing fails until the row goes, and a fixture that starts disagreeing
fails until it is fixed or recorded here. -/
def artBandParityOffences : List (String × String) := []

/-- The judge broken once for each way the band can go, and each way it may
legitimately move. Synthetic trees and stylesheets, built here: the corpus
loop below proves the claim is reached, and these prove it can refuse.

The two controls are the point. `the element and its rule renamed together`
must pass — the claim is parity, not a spelling, and the twenty false
offences this block once recorded came from a check that could not tell the
two apart. `the reference carrying a fallback` must pass for the reason
`Tests/HtmlTokens.lean` records: `var(--name, …)` is a read, and reading
only the bare form is how a painted bar was once called missing. -/
def artBandMutants : List (String × Bool × Bool × String × Array Html.Node × Bool) :=
  let header := Html.elem "header" #[Html.elem "h2" #[Html.text "Title"]]
  let slide (kid : Html.Node) : Array Html.Node :=
    #[Html.elem "section" #[kid] #[("class", "slide")]]
  let live := slide header
  let bandRule (sel : String) : String :=
    sel ++ " { background: var(--frametitlebg);\n  color: var(--frametitlefg, var(--bg, #fff)); }\n"
  [ ("the shape the backend writes", true, true, bandRule "section.slide > header", live, false),
    ("the poster's own carrier instead", true, true,
      bandRule "body > header.headline",
      #[Html.elem "header" #[] #[("class", "headline")]], false),
    ("the bar declared only inside an at-rule", true, true,
      "@media screen {\n" ++ bandRule "section.slide > header" ++ "}\n", live, false),
    ("the reference carrying a fallback", true, true,
      "section.slide > header { background: var(--frametitlebg, #333); }\n", live, false),
    ("the element and its rule renamed together", true, true,
      bandRule "section.slide > div.band-top",
      slide (Html.elem "div" #[] #[("class", "band-top")]), false),
    ("nothing declared and nothing painted", false, false, "", live, false),
    ("the rule gone", true, true, "", live, true),
    ("the element gone", true, true, bandRule "section.slide > header",
      slide (Html.elem "p" #[Html.text "body"]), true),
    ("the rule moved and the element left behind", true, true,
      bandRule "section.slide > div.band-top", live, true),
    ("the element lifted out of the slide", true, true,
      bandRule "section.slide > header", #[header], true),
    ("the property misspelled", true, true,
      "section.slide > header { background: var(--frametitlebackground); }\n", live, true),
    ("the reference off the ground and onto a border", true, true,
      "section.slide > header { border-color: var(--frametitlebg); }\n", live, true),
    ("a rule painting a band the design never declared", false, false,
      bandRule "section.slide > header", live, true),
    ("bytes painting a band the design never declared", true, false, "", live, true),
    ("the selector unreadable", true, true,
      bandRule "section.slide > header + header", live, true)]

/-- Every fixture's painted furniture band held against the HTML the same
document emits, through the one declaration both artifacts read. The judge
is exercised on its own mutants first, so a green corpus is a claim that
has been seen to refuse. -/
def artBandParityChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  t s!"the band's key is a declared consumed role"
    (Ir.Design.consumedRoles.contains artBandRole)
  for (n, _) in artBandParityOffences do
    t s!"band parity offence row {n}: names a golden fixture" (goldenNames.contains n)
  for (label, painted, declared, css, body, wantOffence) in artBandMutants do
    let offs := artBandOffences painted declared css body
    if wantOffence then
      t s!"band parity mutant, {label}: the judge refuses it" (!offs.isEmpty)
    else
      t s!"band parity mutant, {label}: the judge accepts it: {offs.toList}" offs.isEmpty
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut paintedSeen := 0
  let mut declaredSeen := 0
  let mut carriedSeen := 0
  for n in goldenNames do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc
    let out := layoutOf fs doc geom (some pats) store
    match readArtifact (driverPdf fs geom doc out store) with
    | .error e => t s!"band parity {n}: the file reads back: {e}" false
    | .ok pages =>
      -- The band a page paints, read from its own bytes: a fill against the
      -- top edge. The bottom edge is a different band — a chrome footer's
      -- ground — and a different claim: the HTML footer carries no ground at
      -- all, so folding the two would diagnose a painted footer as a missing
      -- title bar. No corpus fixture paints one, so the footer's own parity
      -- is unclaimed here rather than claimed vacuously.
      let painted := pages.any fun p => p.bands.any fun b => b.y1 ≥ p.box.y1
      let declared := (Ir.Design.ofDoc doc).frametitle.isSome
      let (head, body, _) := HtmlDoc.emitTree {} doc
      let css := artTreeCssList (artTreeCssList "" head.toList) body.toList
      if painted then paintedSeen := paintedSeen + 1
      if declared then declaredSeen := declaredSeen + 1
      if declared && !(artBandSelectors css).isEmpty then carriedSeen := carriedSeen + 1
      let offs := artBandOffences painted declared css body
      if artBandParityOffences.any fun (f, _) => f == n then
        t s!"band parity {n}: the recorded offence no longer fires — its two \
artifacts now agree; delete its row" (!offs.isEmpty)
      else
        t s!"band parity {n}: {offs.toList}" offs.isEmpty
  -- Non-vacuity: a claim no fixture reaches proves nothing, and each link
  -- of the chain needs its own witness.
  t s!"band parity: painted bands are reached ({paintedSeen})" (0 < paintedSeen)
  t s!"band parity: declared band pairs are reached ({declaredSeen})" (0 < declaredSeen)
  t s!"band parity: carried bands are reached ({carriedSeen})" (0 < carriedSeen)

/-- The palette role a page's own ground is declared under, and the property
the HTML backend names after it. Keyed on the role for the same reason the
band's claim is: the role is the document's declaration, the element is the
emitter's choice. -/
def artGroundRole : String := "titlepagebg"

/-- Every way a document's two artifacts disagree about a title page's own
declared ground — the same three links as the band, over the other ground
the engine paints. Pure in its four arguments, so the mutants below exercise
the judge the corpus runs.

The `painted` argument is not "some page has a fill": every themed document
fills every page from `bg`. It is "some page ships a full-page fill in the
*declared title-page colour*", which is the only observation that separates a
page carrying its own ground from a page carrying the document's. -/
def artGroundOffences (painted declared : Bool) (css : String)
    (body : Array Html.Node) : Array String := Id.run do
  let mut out : Array String := #[]
  let sels := artGroundSelectors artGroundRole css
  if painted && !declared then
    out := out.push s!"a page paints a full-page ground while the design \
declares no title-page pair: --{artGroundRole} is unset"
  if !sels.isEmpty && !declared then
    out := out.push s!"the stylesheet paints from --{artGroundRole} with no \
title-page pair declared: {sels.toList}"
  if declared then
    unless painted do
      out := out.push s!"the design declares a title-page ground and no page \
ships a full-page fill in it"
    if sels.isEmpty then
      out := out.push s!"the design declares a title-page pair and no rule \
paints a background from --{artGroundRole}"
    else
      let readable := sels.filter fun s => !(artSelChains s).isEmpty
      if readable.isEmpty then
        out := out.push s!"no selector painting the ground resolves to an \
element this check can read: {sels.toList}"
      else unless readable.any fun s =>
          (artSelChains s).any fun c => artChainInList c artBodyPath body.toList do
        out := out.push s!"every rule painting the ground selects an element \
the tree does not ship: {readable.toList}"
  return out

/-- The judge broken once for each way the ground can go, and each way it
may legitimately move — the band block's two controls carried over: a
renamed element with its rule renamed together must pass (the claim is
parity, not a spelling), and a reference with a fallback is a read. -/
def artGroundMutants :
    List (String × Bool × Bool × String × Array Html.Node × Bool) :=
  let title := Html.elem "h1" #[Html.text "Title"]
  let page (cls : String) : Array Html.Node :=
    #[Html.elem "section" #[title] #[("class", cls)]]
  let live := page "slide title-page"
  let groundRule (sel : String) : String :=
    sel ++ " { background: var(--titlepagebg);\n  color: var(--titlepagefg, var(--bg, #fafaf9)); }\n"
  [ ("the shape the backend writes", true, true,
      groundRule "section.slide.title-page", live, false),
    ("the ground declared only inside an at-rule", true, true,
      "@media screen {\n" ++ groundRule "section.slide.title-page" ++ "}\n", live, false),
    ("the reference carrying a fallback", true, true,
      "section.slide.title-page { background: var(--titlepagebg, #101822); }\n",
      live, false),
    ("the element and its rule renamed together", true, true,
      groundRule "section.slide.title-ground",
      page "slide title-ground", false),
    ("nothing declared and nothing painted", false, false, "", live, false),
    ("the rule gone", true, true, "", live, true),
    ("the class gone from the element", true, true,
      groundRule "section.slide.title-page", page "slide", true),
    ("the rule moved and the element left behind", true, true,
      groundRule "section.slide.title-ground", live, true),
    ("the PDF page never painted it", false, true,
      groundRule "section.slide.title-page", live, true),
    ("the property misspelled", true, true,
      "section.slide.title-page { background: var(--titlepageground); }\n",
      live, true),
    ("the reference off the ground and onto a border", true, true,
      "section.slide.title-page { border-color: var(--titlepagebg); }\n",
      live, true),
    ("a rule painting a ground the design never declared", false, false,
      groundRule "section.slide.title-page", live, true),
    ("a page painting a ground the design never declared", true, false, "", live, true),
    ("the selector unreadable", true, true,
      groundRule "section.slide.title-page + section", live, true)]

/-- **A page's ground is declared once and both artifacts paint it.** The
invariant the dark title page rests on, over the corpus and over the judge's
own mutants: the PDF page carries a full-page fill in the declared colour,
the stylesheet paints the same role, and the element the rule selects is in
the tree the same document emits. The PDF half reads `Layout.Out` — the
fill's own colour, which no IR dump carries — and the HTML half the typed
tree, so neither end is a golden's word for it.

The negative direction is the corpus's: no fixture but one declares a
title-page ground, and none of them may paint one or emit a rule for one. -/
def artGroundParityChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  t s!"the ground's key is a declared consumed role"
    (Ir.Design.consumedRoles.contains artGroundRole)
  for (label, painted, declared, css, body, wantOffence) in artGroundMutants do
    let offs := artGroundOffences painted declared css body
    if wantOffence then
      t s!"ground parity mutant, {label}: the judge refuses it" (!offs.isEmpty)
    else
      t s!"ground parity mutant, {label}: the judge accepts it: {offs.toList}"
        offs.isEmpty
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut paintedSeen := 0
  let mut declaredSeen := 0
  let mut carriedSeen := 0
  for n in goldenNames do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc
    let out := layoutOf fs doc geom (some pats) store
    let ground := (Ir.Design.ofDoc doc).titlepage.map (·.bg)
    -- A full-page fill in the *declared* colour: the observation that
    -- separates a page's own ground from the document's, which every themed
    -- fixture also paints full-page.
    let fullPageIn (c : Ir.Color) (p : Layout.PageOut) : Bool :=
      p.fills.any fun f =>
        f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH &&
          f.color == c
    let painted := match ground with
      | some c => out.pages.any (fullPageIn c)
      | none => false
    -- And a page's ground does not leak: exactly one page carries it, which
    -- is what "the title page's" means. Layout restores the ink and the
    -- ground from the palette in force when the frame closes; this is the
    -- artifact's word for that restore.
    if let some c := ground then
      t s!"ground parity {n}: the declared ground is on one page only"
        ((out.pages.filter (fullPageIn c)).size == 1)
    let declared := ground.isSome
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let css := artTreeCssList (artTreeCssList "" head.toList) body.toList
    if painted then paintedSeen := paintedSeen + 1
    if declared then declaredSeen := declaredSeen + 1
    if declared && !(artGroundSelectors artGroundRole css).isEmpty then
      carriedSeen := carriedSeen + 1
    t s!"ground parity {n}: {(artGroundOffences painted declared css body).toList}"
      (artGroundOffences painted declared css body).isEmpty
  t s!"ground parity: painted grounds are reached ({paintedSeen})" (0 < paintedSeen)
  t s!"ground parity: declared grounds are reached ({declaredSeen})" (0 < declaredSeen)
  t s!"ground parity: carried grounds are reached ({carriedSeen})" (0 < carriedSeen)
  -- A title template may lose a node's custom arrangement without losing an
  -- independently readable full-page fill. This deliberately mixes literal
  -- text with the title datum so the built-in title layout stands.
  let mixedSrc :=
    "\\documentclass[aspectratio=169]{beamer}\n" ++
    "\\definecolor{probeNight}{HTML}{202833}\n" ++
    "\\setbeamertemplate{title page}{\\begin{tikzpicture}[remember picture,overlay]" ++
    "\\fill[probeNight] (current page.south west) rectangle (current page.north east);" ++
    "\\node[anchor=west,text=white] at (current page.west) {Label: \\inserttitle};" ++
    "\\end{tikzpicture}\\null}\n" ++
    "\\title{Invented Heading}\\begin{document}\\titlepage\\end{document}\n"
  let (mixedDoc, mixedDs) := elabStr mixedSrc
  let mixedGeom := Layout.Geom.ofPage mixedDoc.page
  let mixedOut := layoutOf oneFace mixedDoc mixedGeom
  let mixedGround : Ir.Color := { r := 0x20, g := 0x28, b := 0x33 }
  let mixedPainted := (mixedOut.pages[0]?.bind (·.fills[0]?)).any fun f =>
    f.x == 0 && f.y == 0 && f.w == mixedGeom.pageW && f.h == mixedGeom.pageH &&
      f.color == mixedGround
  let mixedDeclared := (Ir.Design.ofDoc mixedDoc).titlepage.map (·.bg) == some mixedGround
  let (mixedHead, mixedBody, _) := HtmlDoc.emitTree {} mixedDoc
  let mixedCss := artTreeCssList (artTreeCssList "" mixedHead.toList) mixedBody.toList
  let mixedOffences := artGroundOffences mixedPainted mixedDeclared mixedCss mixedBody
  let mixedLayoutDs := mixedDs.filter (·.code == "W0363")
  t "a mixed title node is one accounting for its fallback and retained ground"
    (mixedLayoutDs.size == 1 && mixedLayoutDs.any fun d =>
      hasStr d.message "custom arrangement falls back" &&
      hasStr d.message "readable full-page ground stays")
  t s!"a readable full-page fill survives title-layout fallback in both artifacts: \
{mixedOffences.toList}"
    (mixedPainted && hasStr mixedCss "--titlepagebg: #202833;" && mixedOffences.isEmpty)

/-! ## A frame's own ground: the palette in force, and both artifacts paint it

The third ground the engine paints, beside the band and the title page: the
plain frame's. reveal.js declares a slide's background per slide
(`data-background-color`); here the declaration already exists — the `bg`
of the palette in force where the frame stands, the document's or a body
`\palette`'s — so the class this block closes is a declared ground one
artifact does not paint. Before it, the paged deck's stage painted the
stylesheet's `--surface` whatever the document declared: a dark declared
ground shipped its light ink on a light stage while the PDF was right, and
a reader in dark mode got a theme's dark ink on the stylesheet's dark
surface. -/

/-- The property a frame's plain ground is declared under: the palette's
`bg`, which `:root` carries for the document and a body epoch redefines on
the node it stands on (`HtmlDoc.withEpoch`). -/
def artStageRole : String := "bg"

/-- The last value a declaration list gives one custom property. -/
def artVarIn (decls : String) (name : String) : Option String :=
  ((decls.splitOn ";").filterMap fun d =>
    match d.splitOn ":" with
    | [k, v] => if k.trimAscii.toString == s!"--{name}" then some v.trimAscii.toString else none
    | _ => none).getLast?

/-- The last value the stylesheet's `:root` blocks give one custom property:
the document's own declaration, which the backend writes after the
colour-scheme defaults. -/
def artRootVar (css : String) (name : String) : Option String :=
  ((artCssBlocks css).filterMap fun (sel, decls) =>
    if sel == ":root" then artVarIn decls name else none).back?

mutual

/-- The plain frames' stages in document order — a `section.slide` that is
neither the standout inversion nor the title page — each with the value the
nearest inline redefinition of the role, on it or on an ancestor, gives it:
where a body epoch's ground lands (the section, or a stepped frame's track;
custom properties inherit). -/
def artStagesOne (inl : Option String) (acc : Array (Option String)) :
    Html.Node → Array (Option String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let own := (attrs.find? (·.1 == "style")).bind fun a => artVarIn a.2 artStageRole
    let inl := own.orElse fun _ => inl
    let cs := (((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " "
    let acc := if t == "section" && cs.contains "slide" && !cs.contains "standout" &&
        !cs.contains "title-page" then acc.push inl else acc
    artStagesList inl acc kids.toList

def artStagesList (inl : Option String) (acc : Array (Option String)) :
    List Html.Node → Array (Option String)
  | [] => acc
  | k :: rest => artStagesList inl (artStagesOne inl acc k) rest

end

/-- The frames' declared grounds in document order, read at the one
resolving site both backends answer to (`Ir.frameGroundOf`). The HTML
plain-stage judge excludes the standout inversion; the PDF frame-number
judge includes it, since a hidden footer does not remove a content frame. -/
def artFrameGrounds (doc : Ir.Doc) (includeStandout : Bool := false) :
    Array (Option Ir.Color) := Id.run do
  let mut pal := doc.palette
  let mut out : Array (Option Ir.Color) := #[]
  for b in doc.body do
    match b with
    | .setPalette p => pal := p
    | .frame _ standout valign _ _ =>
      if (includeStandout || !standout) && !(valign matches .golden) then
        out := out.push (Ir.frameGroundOf pal standout valign)
    | _ => pure ()
  return out

/-- The path a plain stage stands on in the emitted tree. -/
def artStagePath : Array ArtElem := artBodyPath ++ #[("main", #[]), ("section", #["slide"])]

/-- Every way the HTML deck disagrees with the palette in force about a
plain frame's ground and ink: the stage count, the rule painting the stage
from the role, the rule inking it from `--fg`, and each stage's resolved
value against the declared one. Pure in its three arguments, so the mutants
below exercise the judge the corpus runs. -/
def artStageGroundOffences (expected : Array (Option Ir.Color)) (css : String)
    (body : Array Html.Node) : Array String := Id.run do
  let mut out : Array String := #[]
  let stages := artStagesList none #[] body.toList
  if stages.size != expected.size then
    out := out.push s!"{expected.size} plain frames and {stages.size} plain stages"
  if expected.any Option.isSome then
    let blocks := (artCssBlocks css).filter fun (sel, _) =>
      (artSelChains sel).any fun c => artChainMatchesPath c artStagePath
    unless blocks.any fun (_, d) => artPaintsFrom artStageRole d do
      out := out.push s!"no rule paints the plain stage from --{artStageRole}"
    unless blocks.any fun (_, d) => (d.splitOn ";").any fun x =>
        match x.splitOn ":" with
        | [p, v] => p.trimAscii.toString == "color" && hasStr v "var(--fg"
        | _ => false do
      out := out.push "no rule inks the plain stage from --fg"
  let root := artRootVar css artStageRole
  for i in [0:min stages.size expected.size] do
    let got := stages[i]!.orElse fun _ => root
    let want := expected[i]!.map HtmlDoc.cssColor
    if got != want then
      out := out.push s!"plain frame {i + 1}: the stage resolves --{artStageRole} to \
{got}, the palette in force declares {want}"
  return out

/-- A deck whose middle frame stands in a body epoch with its own dark
ground and light ink, restored after: reveal.js's per-slide background,
spelled as the declaration this engine already has. Invented values. -/
def artEpochDeck : String :=
  "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++
  "\\begin{frame}{On the document's ground}\nA first frame.\n\\end{frame}\n" ++
  "\\palette{ bg = #14213D, fg = #F5F5F5, muted = #F5F5F5 }\n" ++
  "\\begin{frame}{On a declared dark ground}\nA second frame.\n\\end{frame}\n" ++
  "\\palette{ bg = #FFFFFF, fg = #000000, muted = #696664 }\n" ++
  "\\begin{frame}{Back on a light ground}\nA third frame.\n\\end{frame}\n" ++
  "\\end{document}\n"

/-- One breakable frame in a dark epoch, taller than its stage: its
continuation page is the frame's page as much as the first, so both stand
on the epoch's ground. Invented values. -/
def artEpochSpillDeck : String :=
  "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++
  "\\palette{ bg = #14213D, fg = #F5F5F5 }\n" ++
  "\\begin{frame}[allowframebreaks]{A frame that continues}\n\\begin{itemize}\n" ++
  String.join ((List.range 24).map fun i => s!"\\item Filler beat {i + 1}.\n") ++
  "\\end{itemize}\n\\end{frame}\n\\end{document}\n"

/-- The judge broken once for each link, and the shape the backend writes
accepted: the rule gone, the rule reading the stylesheet's surface, the
epoch's redefinition dropped, and the ink rule gone. -/
def artStageMutants : List (String × String × Array Html.Node × Bool) :=
  let stage (style : String) : Html.Node :=
    Html.elem "section" #[] (#[("class", "slide")] ++
      (if style.isEmpty then #[] else #[("style", style)]))
  let root := ":root {\n    --bg: #fdfcf9;\n}\n"
  let rule (bg : String) : String :=
    s!"@media screen \{\nsection.slide, section.section-page \{ background: {bg}; \
color: var(--fg, var(--ink)); }\n}\n"
  let live := #[Html.elem "main" #[stage "", stage "--bg: #14213d"]]
  [ ("the shape the backend writes", root ++ rule "var(--bg, var(--surface))", live, false),
    ("the rule gone", root, live, true),
    ("the stage painting the stylesheet's surface", root ++ rule "var(--surface)", live, true),
    ("the epoch's redefinition dropped", root ++ rule "var(--bg, var(--surface))",
      #[Html.elem "main" #[stage "", stage ""]], true),
    ("the ink rule gone", root ++
      "section.slide { background: var(--bg, var(--surface)); }\n", live, true)]

/-- Every page of a counted frame that does not stand on the frame's declared
ground: the PDF half of the stage-ground claim, read off `Layout.Out` — the
fill the page ships first, which `finishPage` prepends whole. A frame on an
undeclared ground ships no full-page fill; a declared one ships its own
colour and not the document's. -/
def artPageGroundOffences (geom : Layout.Geom) (expected : Array (Option Ir.Color))
    (pages : Array Layout.PageOut) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut i := 0
  for p in pages do
    i := i + 1
    let some k := p.frame | continue
    let some want := expected[k - 1]? | do
      out := out.push s!"page {i} names frame {k} without a declared ground entry"
      continue
    let ground := p.fills[0]?.bind fun f =>
      if f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH then some f.color
      else none
    if ground != want then
      out := out.push s!"page {i} (frame {k}) ships the ground \
{ground.map HtmlDoc.cssColor}, the palette in force declares {want.map HtmlDoc.cssColor}"
  return out

/-- **A plain frame's ground is the palette in force, and both artifacts
paint it.** Over the judge's own mutants, the slides fixtures of the corpus,
and the epoch deck: every plain stage resolves the role to the declared
value of the palette in force at its frame, through a rule that paints the
stage from it and inks the stage from `--fg`; and every PDF page of that
frame ships the same colour as its ground. -/
def artStageGroundChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let want : Array (Option Ir.Color) :=
    #[some { r := 0xFD, g := 0xFC, b := 0xF9 }, some { r := 0x14, g := 0x21, b := 0x3D }]
  for (label, css, body, wantOffence) in artStageMutants do
    let offs := artStageGroundOffences want css body
    if wantOffence then
      t s!"stage ground mutant, {label}: the judge refuses it" (!offs.isEmpty)
    else
      t s!"stage ground mutant, {label}: the judge accepts it: {offs.toList}" offs.isEmpty
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut judged := 0
  let mut declared := 0
  for n in goldenNames do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    unless doc.docClass == .slides do continue
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let css := artTreeCssList (artTreeCssList "" head.toList) body.toList
    let expected := artFrameGrounds doc
    judged := judged + 1
    if expected.any Option.isSome then declared := declared + 1
    let offs := artStageGroundOffences expected css body
    t s!"stage ground {n}: {offs.toList}" offs.isEmpty
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let out := layoutOf fs doc geom none (← corpusStore doc)
    let pageOffs := artPageGroundOffences geom (artFrameGrounds doc true) out.pages
    t s!"stage ground {n} pdf: {pageOffs.toList}" pageOffs.isEmpty
  t s!"stage ground: slides fixtures are judged ({judged})" (0 < judged)
  t s!"stage ground: declared grounds are reached ({declared})" (0 < declared)
  let (edoc, eds) := elabStr artEpochDeck
  t s!"stage ground epoch deck elaborates clean: {eds.toList.map (·.code)}" eds.isEmpty
  let expected := artFrameGrounds edoc
  t "stage ground epoch deck: the middle frame declares its own ground"
    (expected == #[(edoc.palette.find? "bg"), some { r := 0x14, g := 0x21, b := 0x3D }, some { r := 0xFF, g := 0xFF, b := 0xFF }])
  let (ehead, ebody, _) := HtmlDoc.emitTree {} edoc
  let ecss := artTreeCssList (artTreeCssList "" ehead.toList) ebody.toList
  let offs := artStageGroundOffences expected ecss ebody
  t s!"stage ground epoch deck html: {offs.toList}" offs.isEmpty
  let egeom := Layout.Geom.ofPage edoc.page
  let eout := layoutOf oneFace edoc egeom
  t s!"stage ground epoch deck: one page per frame ({eout.pages.size})" (eout.pages.size == 3)
  let pageOffs := artPageGroundOffences egeom (artFrameGrounds edoc true) eout.pages
  t s!"stage ground epoch deck pdf: {pageOffs.toList}" pageOffs.isEmpty
  let (sdoc, _) := elabStr artEpochSpillDeck
  let sgeom := Layout.Geom.ofPage sdoc.page
  let sout := layoutOf oneFace sdoc sgeom
  t s!"stage ground spill deck: the frame continues ({sout.pages.size} pages)"
    (sout.pages.size ≥ 2 && sout.pages.all (·.frame == some 1))
  let spillOffs := artPageGroundOffences sgeom (artFrameGrounds sdoc true) sout.pages
  t s!"stage ground spill deck pdf: {spillOffs.toList}" spillOffs.isEmpty
  let (mixed, _) := elabStr (deck169 "\\theme{moloch}"
    ("\\begin{frame}{Before}FirstBody\\end{frame}\n" ++
     "\\begin{frame}[standout]{Aside}AsideBody\\end{frame}\n" ++
     "\\begin{frame}{After}LastBody\\end{frame}"))
  let mgeom := Layout.Geom.ofPage mixed.page
  let mout := layoutOf oneFace mixed mgeom
  let mgrounds := artFrameGrounds mixed true
  t "stage ground: a counted standout keeps its own inversion between ordinary frames"
    (mgrounds == #[mixed.palette.find? "bg", some (Ir.Design.ofDoc mixed).standout.bg,
        mixed.palette.find? "bg"] &&
      mout.pages.map (·.frame) == #[some 1, some 2, some 3] &&
      (artPageGroundOffences mgeom mgrounds mout.pages).isEmpty)
  let missingFill := mout.pages.mapIdx fun i p => if i == 1 then { p with fills := #[] } else p
  t "stage ground: the PDF judge rejects a missing standout fill and an unknown frame"
    (!(artPageGroundOffences mgeom mgrounds missingFill).isEmpty &&
      !(artPageGroundOffences mgeom #[] mout.pages).isEmpty)
  -- beamer's own spelling of the ground: `background canvas`'s bg is the
  -- canvas fill (the default template's full-page rule), so in the preamble
  -- it declares the document's ground and in the body an epoch's.
  let canvas := "\\setbeamercolor{background canvas}{bg=#F0E8D8}\n"
  let frame (s : String) := s!"\\begin\{frame}\{{s}}\nx\n\\end\{frame}\n"
  let (pdoc, pds) := elabStr ("\\documentclass{beamer}\n" ++ canvas ++
    "\\begin{document}\n" ++ frame "One" ++ "\\end{document}\n")
  t s!"background canvas in the preamble declares the document's ground: {pds.toList.map (·.code)}"
    (pdoc.palette.find? "bg" == some { r := 0xF0, g := 0xE8, b := 0xD8 } &&
     pds.all (·.severity == .note))
  let (bdoc, bds) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n" ++
    frame "One" ++ canvas ++ frame "Two" ++ "\\end{document}\n")
  t s!"background canvas in the body declares the frames after it: {bds.toList.map (·.code)}"
    (artFrameGrounds bdoc == #[bdoc.palette.find? "bg", some { r := 0xF0, g := 0xE8, b := 0xD8 }] &&
     bds.all (·.severity == .note))
  let bgeom := Layout.Geom.ofPage bdoc.page
  let bOffs := artPageGroundOffences bgeom (artFrameGrounds bdoc true) (layoutOf oneFace bdoc bgeom).pages
  let (bhead, bbody, _) := HtmlDoc.emitTree {} bdoc
  let bcss := artTreeCssList (artTreeCssList "" bhead.toList) bbody.toList
  let bHtml := artStageGroundOffences (artFrameGrounds bdoc) bcss bbody
  t s!"background canvas in the body reaches both artifacts: {bOffs.toList} {bHtml.toList}"
    (bOffs.isEmpty && bHtml.isEmpty)
  t "background canvas has no ink: its fg is named, not taken"
    (warnCodes ("\\documentclass{beamer}\n\\setbeamercolor{background canvas}{fg=#101010}\n" ++
      "\\begin{document}\n" ++ frame "One" ++ "\\end{document}\n") == ["W0104"])



/-! ## The pitch the artifact declares

`Font.classify` reads a face's `post.isFixedPitch`, and two artifact fields
carry that answer to a reader: the FixedPitch flag of the PDF's font
descriptor (ISO 32000-2 §9.8.2, Table 121: bit position 1, value 1) and the
generic that closes an HTML slot stack (`HtmlDoc.genericFor`). The rows
pinning `classify` read the cause; these read the files, built by the
driver in an environment of its own — a private cache, an empty home, a
`PATH` holding nothing — from faces the corpus ships.

`fonts.tex`'s own stacks cannot witness the pitch: its mono slot closes
with `monospace` through the slot's declared kind whatever the flag says,
and its body and sans faces are proportional. So the stack's claim is read
off a page whose *body* family is the monospace face, where the generic is
the pitch's to decide. -/

/-- Every font descriptor a written PDF carries: its `/FontName` and its
`/Flags`. -/
def artDescriptorFlags (pdf : ByteArray) : Except String (Array (String × Int)) := do
  let es := (← PdfRead.objects pdf).val
  return es.filterMap fun e =>
    if e.val.get? "Type" == some (.name "FontDescriptor") then
      match e.val.get? "FontName", (e.val.get? "Flags").bind Obj.int? with
      | some (.name n), some f => some (n, f)
      | _, _ => none
    else none

/-- The generic that closes a page's `--font-<slot>` stack, read from the
last declaration — the one the cascade keeps. -/
def artStackGeneric (html slot : String) : Option String := do
  let parts := html.splitOn ("--font-" ++ slot ++ ": ")
  if parts.length < 2 then none
  let decl ← parts.getLast?
  let stack ← (decl.splitOn ";").head?
  ((stack.splitOn ",").getLast?).map (·.trimAscii.toString)

def artifactPitchChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"artifact pitch: leantex builds:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode != 0 then return
  let dir ← IO.FS.createTempDir
  IO.FS.createDirAll (dir / "fonts")
  IO.FS.createDirAll (dir / "home")
  for e in ← (System.FilePath.mk testFonts).readDir do
    if e.fileName.endsWith ".otf" || e.fileName.endsWith ".ttf" then
      IO.FS.writeBinFile (dir / "fonts" / e.fileName) (← IO.FS.readBinFile e.path)
  IO.FS.writeFile (dir / "fonts.tex") (← IO.FS.readFile "testdata/corpus/fonts.tex")
  let page (body : String) : String :=
    "\\documentclass{article}\n\\fonts{ dir = \"fonts\", body = \"" ++ body ++ "\" }\n" ++
    "\\output{ formats = html }\n\\begin{document}\nPlain words.\n\\end{document}\n"
  IO.FS.writeFile (dir / "codebody.tex") (page "Source Code Pro")
  IO.FS.writeFile (dir / "serifbody.tex") (page "Source Serif Pro")
  let run (name : String) : IO (UInt32 × String) := do
    let p ← IO.Process.output
      { cmd := ".lake/build/bin/leantex"
        args := #[(dir / s!"{name}.tex").toString, "-o", (dir / "out").toString ++ "/"]
        env := #[("XDG_CACHE_HOME", some (dir / "cache").toString),
          ("HOME", some (dir / "home").toString), ("PATH", some (dir / "no-tools").toString),
          ("LEANTEX_FONT_PATH", none), ("LEANTEX_FONT", none)] }
    return (p.exitCode, p.stdout ++ p.stderr)
  let (code, log) ← run "fonts"
  t s!"artifact pitch: fonts.tex builds: {log}" (code == 0)
  match artDescriptorFlags (← IO.FS.readBinFile (dir / "out" / "fonts.pdf")) with
  | .error e => t s!"artifact pitch: fonts.pdf reads back: {e}" false
  | .ok fds =>
    let flagsOf (n : String) : Option Int := (fds.find? (artBaseName ·.1 == n)).map (·.2)
    t s!"artifact pitch: fonts.pdf declares Source Code Pro fixed-pitch: {fds}"
      ((flagsOf "SourceCodePro-Regular").map (· % 2 == 1) == some true)
    t s!"artifact pitch: fonts.pdf declares Source Serif Pro proportional: {fds}"
      ((flagsOf "SourceSerifPro-Regular").map (· % 2 == 0) == some true)
  for (name, want) in [("codebody", "monospace"), ("serifbody", "serif")] do
    let (code, log) ← run name
    t s!"artifact pitch: {name}.tex builds: {log}" (code == 0)
    let html ← IO.FS.readFile (dir / "out" / s!"{name}.html")
    let got := artStackGeneric html "body"
    t s!"artifact pitch: {name}.html closes the body stack with {want}: {got}"
      (got == some want)
  IO.FS.removeDirAll dir


/-! ## Kerns reach the page

The layout folds each GPOS pair kern into the advance of the glyph before
it, and the writer places every glyph by that advance
(`Pdf.place_between`). Three claims, read from the written bytes by the
evaluator's pen — never the layout's record of where it meant to paint:
every glyph starts where the layout put it; a run after a font change
starts at or after the rendered end of the run before it; a centred line
is centred as painted. The defect they pin: kerns never reached the file
(the writer painted nominal widths and believed its pen was where the
layout was), so the drift since the last `Tm` was absorbed at the next
absolute one — an italic word stood 8.46 pt inside the upright word
before it, and a centred line of kerned pairs painted 8.6 pt wider than it
measured, 4.3 pt off its axis. -/

/-- A kerning face and its italic in every slot: Source Serif Pro, whose
"Ta" pair is −41/1000 em (hb-shape's number, pinned in `FontMath`). -/
def artKernSet : IO Font.FontSet := do
  let load (f : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ f)) with
    | .ok font => pure font
    | .error e => throw (IO.userError s!"{f}: {e}")
  let reg ← load "SourceSerifPro-Regular.otf"
  let ital ← load "SourceSerifPro-RegularIt.otf"
  return { fonts := #[reg, ital]
           index := ((List.range 3).flatMap fun slot =>
             [((slot, 400, false), 0), ((slot, 700, false), 0),
              ((slot, 400, true), 1), ((slot, 700, true), 1)]).toArray }

/-- Pairs the face kerns hard, an italic word right after them, a second
justified line with another, and a centred line of kerned pairs. -/
def artKernSrc : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++
  "Ta Ta Ta To To Te Te Ya Ya AV AV AV Wa Wa \\emph{Tote} end. " ++
  "Yo Yo Tw Tw Ty Vo Vo Wo Wo LT LT Ly Ly To Te Ta and \\emph{Wave} Ta To, Ty Tw Yo.\n" ++
  "\\begin{center}\nTaTaTaTaTaTaTaTaTaTa\n\\end{center}\n\\end{document}\n"

/-- Runs that start inside the rendered extent of the run before them on
the same baseline in another face: where a font change once absorbed the
kerns dropped before it. Within one face a positive `TJ` number is a kern
and may pull a string back over the last one's advance box; across a
face change nothing may. -/
def artFaceChangeOffences (pages : Array ArtPage) : Array String := Id.run do
  let mut out : Array String := #[]
  for h : i in [0:pages.size] do
    let rs := pages[i].runs
    for k in [1:rs.size] do
      let a := rs[k - 1]!
      let b := rs[k]!
      if a.y == b.y && a.face != b.face && b.x < a.x1 - artSpellSlack then
        out := out.push
          s!"page {i + 1}: '{b.text}' starts {(a.x1 - b.x).toPtString}pt inside '{a.text}'"
  return out

def kernPlacementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let fs ← artKernSet
  let (doc, _) := elabStr artKernSrc
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fs doc geom
  match readArtifact (driverPdf fs geom doc out) with
  | .error e => t s!"kerns: the kerned page reads back: {e}" false
  | .ok pages =>
    t "kerns: the fixture ships one page" (pages.size == 1 && out.pages.size == 1)
    let laid := out.pages.flatMap (artLaidGlyphs geom)
    let offs := artGlyphPlacementOffences laid (pages.flatMap artPaintedGlyphs)
    t s!"kerns: every glyph starts where the layout put it: {offs.toList.take 5}"
      (!laid.isEmpty && offs.isEmpty)
    let faceOffs := artFaceChangeOffences pages
    t s!"kerns: a run after a font change starts at or after the run before it: {faceOffs.toList}"
      faceOffs.isEmpty
    t "kerns: the fixture changes face on a baseline (the claim is not vacuous)"
      (pages.any fun p => (List.range (p.runs.size - 1)).any fun k =>
        p.runs[k]!.y == p.runs[k + 1]!.y && p.runs[k]!.face != p.runs[k + 1]!.face)
    -- The centred line: the page's lowest body baseline, its painted extent
    -- centred on the measure.
    let body := pages[0]!.runs.filter (!·.isArtifact)
    let lowest := body.foldl (fun m r => min m r.y) (body[0]?.map (·.y) |>.getD 0)
    let line := body.filter (·.y == lowest)
    let x0 := line.foldl (fun m r => min m r.x) (line[0]?.map (·.x) |>.getD 0)
    let x1 := line.foldl (fun m r => max m r.x1) 0
    let area := artBodyArea geom
    let off := (x0 + x1) - (area.x0 + area.x1)
    t s!"kerns: the centred line is centred as painted ({(off / 2).toPtString}pt off its axis)"
      (!line.isEmpty && off.natAbs ≤ 2 * artSpellSlack.natAbs)
