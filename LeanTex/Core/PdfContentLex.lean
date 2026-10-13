module

public import LeanTex.Core.PdfObj

/-! The content-stream tokenizer (ISO 32000-2 §7.8.2), total over arbitrary bytes: operands through
the object reader, operators, and inline images. -/

namespace LeanTex.Core.PdfContentLex

open LeanTex.Core.PdfRead (Obj)
open LeanTex.Core.PdfLex

/-- One token of a content stream: an operand, an operator, or an inline image with its dictionary
and verbatim data. -/
public inductive Tok where
  | val (o : Obj)
  | op (name : String)
  | inline (dict : Array (String × Obj)) (data : ByteArray)
  deriving Inhabited

/-- A regular character (§7.2.2) inside the file: neither white space nor a delimiter. -/
@[expose] public def regular (c : Nat) : Bool := c != 256 && !isWs c && !isDelim c

/-- Where the run of regular characters that starts at `i` ends. -/
public def runEnd (b : ByteArray) (i : Nat) : Nat :=
  (forIn [0:b.size + 1] i (fun _ j =>
    pure (if regular (at? b j) then ForInStep.yield (j + 1) else .done j)) : Id Nat).run

/-- The bytes `[i, j)` as the ASCII string an operator is. -/
@[expose] public def asciiAt (b : ByteArray) (i j : Nat) : String :=
  String.ofList ((List.range (j - i)).map fun k => Char.ofNat (at? b (i + k)))

/-- A number token's object (§7.3.3): a real where it holds a point, an integer where it reads as
one, else `none`. -/
@[expose] public def numberObj (raw : String) : Option Obj :=
  if raw.contains '.' then some (.real raw) else raw.toInt?.map .int

/-- The component count of an inline image's colour space (§8.9.7, Table 93); `none` for a named resource. -/
public def inlineComponents : Obj → Option Nat
  | .name n =>
    if n == "G" || n == "DeviceGray" || n == "I" || n == "Indexed" then some 1
    else if n == "RGB" || n == "DeviceRGB" then some 3
    else if n == "CMYK" || n == "DeviceCMYK" then some 4
    else none
  | .arr xs =>
    match (xs[0]? : Option Obj) with
    | some (.name n) => if n == "I" || n == "Indexed" then some 1 else none
    | _ => none
  | _ => none

/-- An inline image dictionary's value under either of its two keys. -/
public def inlineGet (d : Array (String × Obj)) (k abbr : String) : Option Obj :=
  ((d.find? (·.1 == abbr)).map (·.2)).orElse fun _ => (d.find? (·.1 == k)).map (·.2)

/-- How many bytes an unfiltered inline image holds, when its dictionary says (§8.9.7). -/
public def inlineLength (d : Array (String × Obj)) : Option Nat := do
  if (inlineGet d "Filter" "F").isSome then none
  let w ← (inlineGet d "Width" "W").bind Obj.int?
  let h ← (inlineGet d "Height" "H").bind Obj.int?
  let mask := inlineGet d "ImageMask" "IM" == some (.bool true)
  let bpc ← if mask then some 1 else (inlineGet d "BitsPerComponent" "BPC").bind Obj.int?
  let comps ← if mask then some 1 else inlineComponents ((inlineGet d "ColorSpace" "CS").getD .null)
  guard (0 < w && 0 < h && 0 < bpc)
  return (w.toNat * bpc.toNat * comps + 7) / 8 * h.toNat

/-- Whether `EI` stands at `e + 1`, after white space at `e` and before
white space, a delimiter or the end. -/
@[expose] public def eiAt (b : ByteArray) (e : Nat) : Bool :=
  isWs (at? b e) && at? b (e + 1) == 69 && at? b (e + 2) == 73 &&
    (let c := at? b (e + 3); c == 256 || isWs c || isDelim c)

/-- The first `EI` marker at or after `i`: where the data ends. -/
public def eiFrom (b : ByteArray) (i : Nat) : Option Nat :=
  (forIn [0:b.size + 1] (i, (none : Option Nat)) (fun _ (j, _) =>
    pure (if j ≥ b.size then ForInStep.done (j, none)
      else if eiAt b j then .done (j, some j) else .yield (j + 1, none))) : Id (Nat × Option Nat)).run.2

/-- An inline image's data from `start` and the position after `EI`: its stated length when `EI`
follows it, else up to the first `EI`. -/
public def inlineData (b : ByteArray) (d : Array (String × Obj)) (start : Nat) :
    Option (ByteArray × Nat) :=
  let byLength : Option (ByteArray × Nat) := do
    let n ← inlineLength d
    let e := start + n
    guard (e ≤ b.size)
    let k := skipWs b e
    guard (at? b k == 69 && at? b (k + 1) == 73 &&
      (let c := at? b (k + 2); c == 256 || isWs c || isDelim c))
    return (b.extract start e, k + 2)
  byLength.orElse fun _ => do
    let e ← eiFrom b start
    return (b.extract start e, e + 3)

/-- An inline image's dictionary from after `BI`, and the position just past `ID`. -/
public def inlineDict (b : ByteArray) (i : Nat) : Option (Array (String × Obj) × Nat) :=
  let r := (forIn [0:b.size + 1] (i, (#[] : Array (String × Obj)), (none : Option Nat))
    (fun _ (j, es, _) =>
      let k := skipWs b j
      match keywordAt b k "ID" with
      | some after => pure (ForInStep.done (after, es, some after))
      | none =>
        match PdfRead.parseVal b k with
        | .ok (.name key, j1) =>
          match PdfRead.parseVal b j1 with
          | .ok (v, j2) =>
            if j2 > k then pure (.yield (j2, es.push (key, v), none))
            else pure (.done (j2, es, none))
          | .error _ => pure (.done (j1, es, none))
        | _ => pure (.done (k, es, none))) : Id (Nat × Array (String × Obj) × Option Nat)).run
  r.2.2.map fun after => (r.2.1, after)

/-- The tokenizer's state: where it stands and what it has read. -/
public structure State where
  pos : Nat
  out : Array Tok
  deriving Inhabited

/-- Whether a byte starts an operand the object reader reads: a string, dictionary, array or name. -/
@[expose] public def objStart (c : Nat) : Bool := c == 40 || c == 60 || c == 91 || c == 47

/-- One step: white space and comments skipped, then one token read, or one byte that starts none skipped. -/
public def step (b : ByteArray) (s : State) : ForInStep State :=
  let i := skipWs b s.pos
  if b.size ≤ i then .done { s with pos := i } else
  let c := at? b i
  if numByte c then
    let (raw, j) := scanNumber b i
    match numberObj raw with
    | some o => .yield { pos := max j (i + 1), out := s.out.push (.val o) }
    | none => .yield { pos := max j (i + 1), out := s.out }
  else if objStart c then
    match PdfRead.parseVal b i with
    | .ok (o, j) =>
      if i < j then .yield { pos := j, out := s.out.push (.val o) }
      else .yield { s with pos := i + 1 }
    | .error _ => .yield { s with pos := i + 1 }
  else if regular c then
    let j := runEnd b i
    let name := asciiAt b i j
    if name == "true" then .yield { pos := j, out := s.out.push (.val (.bool true)) }
    else if name == "false" then .yield { pos := j, out := s.out.push (.val (.bool false)) }
    else if name == "null" then .yield { pos := j, out := s.out.push (.val .null) }
    else if name == "BI" then
      match inlineDict b j with
      | some (d, afterId) =>
        -- §8.9.7: a single white-space byte separates `ID` from the data.
        let start := if isWs (at? b afterId) then afterId + 1 else afterId
        match inlineData b d start with
        | some (data, after) =>
          .yield { pos := max after (j + 1), out := s.out.push (.inline d data) }
        | none => .done { pos := b.size, out := s.out }
      | none => .yield { pos := j, out := s.out.push (.op name) }
    else .yield { pos := max j (i + 1), out := s.out.push (.op name) }
  else .yield { s with pos := i + 1 }

/-- A content stream's tokens, in order. -/
public def scan (b : ByteArray) : Array Tok :=
  ((forIn [0:b.size + 2] ({ pos := 0, out := #[] } : State)
    (fun _ s => pure (step b s)) : Id State).run).out

/-- A token's bytes onto `acc`. -/
public def Tok.renderInto (acc : ByteArray) : Tok → ByteArray
  | .val o => acc ++ o.render
  | .op n => acc ++ n.toUTF8
  | .inline d data =>
    let head := d.foldl (fun a (k, v) =>
      (a ++ (Obj.name k).render).push 32 ++ v.render |>.push 32) (acc ++ "BI ".toUTF8)
    (head ++ "ID ".toUTF8 ++ data).push 10 ++ "EI".toUTF8

/-- Tokens spelled one after another, a line feed after each. -/
public def render (toks : Array Tok) : ByteArray :=
  toks.foldl (fun acc t => (t.renderInto acc).push 10) ByteArray.empty

/-- A number operand's sign, digits as one natural, and the power of ten they stand over (§7.3.3). -/
public def numParts? (o : Obj) : Option (Bool × Nat × Nat) :=
  match o with
  | .int n => some (decide (n < 0), n.natAbs, 1)
  | .real raw =>
    let (neg, s) := match raw.toList with
      | '-' :: rest => (true, rest)
      | '+' :: rest => (false, rest)
      | s => (false, s)
    (digitsOf s 0 1 false false).map fun (n, scale) => (neg, n, scale)
  | _ => none
where
  /-- A real's digits and point read onto `n` and `scale`; `none` past any other character or with no digit. -/
  digitsOf : List Char → Nat → Nat → Bool → Bool → Option (Nat × Nat)
    | [], n, scale, _, seen => if seen then some (n, scale) else none
    | c :: rest, n, scale, dot, seen =>
      if c.isDigit then digitsOf rest (n * 10 + (c.toNat - 48)) (if dot then scale * 10 else scale) dot true
      else if c == '.' && !dot then digitsOf rest n scale true seen
      else none

/-- A number operand as an exact rational (`numParts?`). -/
public def numRat? (o : Obj) : Option Rat :=
  (numParts? o).map fun (neg, n, scale) =>
    let v : Rat := mkRat n scale
    if neg then -v else v

public theorem numRat?_parts (o : Obj) : numRat? o = (numParts? o).map fun (neg, n, scale) =>
    let v : Rat := mkRat n scale
    if neg then -v else v := by
  unfold numRat?
  rfl

/-- A string operand's bytes with its escapes resolved (§7.3.4). -/
public def strBytes? (o : Obj) : Option ByteArray :=
  match o with
  | .str raw =>
    if raw.size ≥ 2 && raw[0]? == some 60 then some (Id.run do
      let mut out := ByteArray.empty
      let mut hi : Option Nat := none
      for k in [1:raw.size - 1] do
        match hexVal ((raw[k]?.map UInt8.toNat).getD 0) with
        | some v =>
          match hi with
          | some h =>
            out := out.push (UInt8.ofNat (h * 16 + v))
            hi := none
          | none => hi := some v
        | none => pure ()
      if let some h := hi then out := out.push (UInt8.ofNat (h * 16))
      return out)
    else if raw.size ≥ 2 && raw[0]? == some 40 then some (Id.run do
      let mut out := ByteArray.empty
      let mut k := 1
      let stop := raw.size - 1
      for _ in [0:raw.size] do
        if k ≥ stop then break
        let c := (raw[k]?.map UInt8.toNat).getD 0
        if c == 92 then
          let d := (raw[k + 1]?.map UInt8.toNat).getD 0
          if 48 ≤ d && d ≤ 55 then
            let mut v := 0
            let mut n := 0
            for _ in [0:3] do
              let e := (raw[k + 1 + n]?.map UInt8.toNat).getD 0
              if n < 3 && k + 1 + n < stop && 48 ≤ e && e ≤ 55 then
                v := v * 8 + (e - 48)
                n := n + 1
            out := out.push (UInt8.ofNat (v % 256))
            k := k + 1 + n
          else if d == 110 then out := out.push 10; k := k + 2
          else if d == 114 then out := out.push 13; k := k + 2
          else if d == 116 then out := out.push 9; k := k + 2
          else if d == 98 then out := out.push 8; k := k + 2
          else if d == 102 then out := out.push 12; k := k + 2
          else if d == 13 then
            k := if (raw[k + 2]?.map UInt8.toNat) == some 10 then k + 3 else k + 2
          else if d == 10 then k := k + 2
          else out := out.push (UInt8.ofNat d); k := k + 2
        else if c == 13 then
          -- §7.3.4.2: an end-of-line marker in a literal is a line feed.
          out := out.push 10
          k := if (raw[k + 1]?.map UInt8.toNat) == some 10 then k + 2 else k + 1
        else
          out := out.push (UInt8.ofNat c)
          k := k + 1
      return out)
    else none
  | _ => none

end LeanTex.Core.PdfContentLex
