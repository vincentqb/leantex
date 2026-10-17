module

public import Std.Data.HashSet
import LeanTex.Core.Hex

/-! JSON values (RFC 8259) read, compressed and laid out as Lean's own `Lean.Json` reads, compresses
and lays them out. -/

namespace LeanTex.Core.JsonText

/-- A JSON number as Lean's `JsonNumber` holds it: `mantissa / 10 ^ exponent`. -/
public structure JsonNumber where
  mantissa : Int
  exponent : Nat
  deriving BEq, Inhabited, Repr

/-- A JSON value; an object's members are sorted by key, each key once. -/
public inductive Json where
  | null
  | bool (b : Bool)
  | num (n : JsonNumber)
  | str (s : String)
  | arr (elems : Array Json)
  | obj (members : Array (String × Json))
  deriving Inhabited

namespace JsonNumber

/-- `n`'s decimal digits, one at least. -/
def countDigits (n : Nat) (digits : Nat := 1) : Nat :=
  if n ≤ 9 then digits else countDigits (n / 10) (digits + 1)
termination_by n
decreasing_by omega

/-- The number as Lean's `JsonNumber.toString` spells it. -/
public protected def toString : JsonNumber → String
  | ⟨m, 0⟩ => m.repr
  | ⟨m, e⟩ =>
    let sign := if m ≥ 0 then "" else "-"
    let m := m.natAbs
    let exp : Int := 9 + countDigits m - (e : Int)
    let exp := if exp < 0 then exp else 0
    let e' := 10 ^ (e - exp.natAbs)
    let left := (m / e').repr
    if m % e' = 0 && exp = 0 then s!"{sign}{left}"
    else
      let right := ((e' + m % e').repr.drop 1).dropEndWhile (· == '0') |>.toString
      let exp := if exp = 0 then "" else "e" ++ exp.repr
      s!"{sign}{left}.{right}{exp}"

/-- The number with its decimal point `s` places to the right. -/
def shiftl : JsonNumber → Nat → JsonNumber
  | ⟨m, e⟩, s => ⟨m * (10 ^ (s - e) : Nat), e - s⟩

/-- The number with its decimal point `s` places to the left. -/
def shiftr : JsonNumber → Nat → JsonNumber
  | ⟨m, e⟩, s => ⟨m, e + s⟩

end JsonNumber

namespace Json

/-! Spelling. -/

/-- One character of a string literal as Lean's `Json.escape` spells it. -/
def escapeStep (acc : String) (c : Char) : String :=
  if c == '"' then acc ++ "\\\""
  else if c == '\\' then acc ++ "\\\\"
  else if c == '\n' then acc ++ "\\n"
  else if c == '\r' then acc ++ "\\r"
  else if 0x20 ≤ c.val then acc.push c
  else
    let code := Hex.digits false 4 c.toNat
    acc ++ "\\u" ++ code

/-- Whether a byte from `i` on is one `escapeStep` changes: a control character, `"` or `\`. -/
def escapesFrom (s : String) (i : Nat) : Bool :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ (String.Pos.Raw.lt_iff.mpr h)
    if b < 32 || b == 34 || b == 92 then true else escapesFrom s (i + 1)
  else false
termination_by s.utf8ByteSize - i

/-- `s` as a JSON string literal after `acc`, as Lean's `Json.renderString` spells it. -/
public def renderString (s : String) (acc : String := "") : String :=
  let acc := acc ++ "\""
  let acc := if escapesFrom s 0 then s.foldl escapeStep acc else acc ++ s
  acc ++ "\""

/-- The value onto `acc` with no white space, an object's members in key order, as Lean's
`Json.compress` spells it. -/
def compressOnto (acc : String) : Json → String
  | .null => acc ++ "null"
  | .bool true => acc ++ "true"
  | .bool false => acc ++ "false"
  | .num n => acc ++ n.toString
  | .str s => renderString s acc
  | .arr elems =>
    let body := elems.attach.foldl (init := (acc ++ "[", true)) fun (out, first) ⟨e, _⟩ =>
      (compressOnto (if first then out else out ++ ",") e, false)
    body.1 ++ "]"
  | .obj kvs =>
    let body := kvs.attach.foldl (init := (acc ++ "{", true)) fun (out, first) ⟨(k, v), _⟩ =>
      (compressOnto (renderString k (if first then out else out ++ ",") ++ ":") v, false)
    body.1 ++ "}"
termination_by j => sizeOf j
decreasing_by
  all_goals simp_wf
  · have := Array.sizeOf_lt_of_mem ‹_ ∈ elems›; omega
  · have := Array.sizeOf_lt_of_mem ‹_ ∈ kvs›; simp at this; omega

/-- The value with no white space, as Lean's `Json.compress` spells it. -/
public def compress (j : Json) : String := compressOnto "" j

/-- The value as Lean's `Json.render` lays it out. -/
public def render : Json → Std.Format
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num n => n.toString
  | .str s => renderString s
  | .arr elems =>
    let elems := Std.Format.joinSep (elems.attach.map fun ⟨e, _⟩ => render e).toList
      ("," ++ Std.Format.line)
    Std.Format.bracket "[" elems "]"
  | .obj kvs =>
    let kvs := Std.Format.joinSep (kvs.attach.foldl (fun acc ⟨(k, v), _⟩ =>
      Std.Format.group (renderString k ++ ":" ++ Std.Format.line ++ render v) :: acc) [])
      ("," ++ Std.Format.line)
    Std.Format.bracket "{" kvs "}"
termination_by j => sizeOf j
decreasing_by
  all_goals simp_wf
  · have := Array.sizeOf_lt_of_mem ‹_ ∈ elems›; omega
  · have := Array.sizeOf_lt_of_mem ‹_ ∈ kvs›; simp at this; omega

/-- The value as Lean's `Json.pretty` lays it out at eighty columns. -/
public def pretty (j : Json) : String := Std.Format.pretty (render j) 80

/-- An object's members as Lean's `Std.TreeMap.Raw.insert` leaves them: sorted by key, each key
holding its last value. -/
def settle (members : Array (String × Json)) : Array (String × Json) := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut kept : Array (String × Json) := #[]
  for m in members.reverse do
    unless seen.contains m.1 do
      seen := seen.insert m.1
      kept := kept.push m
  return kept.qsort fun a b => a.1 < b.1

/-- An object of these members, a later spelling of a key replacing an earlier one. -/
public def mkObj (members : List (String × Json)) : Json := .obj (settle members.toArray)

/-! Reading. -/

/-- A failure as Lean's parser names it: the byte offset it stands at and its message. -/
structure Failure where
  pos : Nat
  msg : String

def endOfInput : String := "unexpected end of input"

/-- The byte at `i`, if the text holds one. -/
def byteAt? (s : String) (i : Nat) : Option UInt8 :=
  if h : i < s.utf8ByteSize then some (s.getUTF8Byte ⟨i⟩ (String.Pos.Raw.lt_iff.mpr h)) else none

/-- The character at `i` and the offset after it, as Lean's parser's `any` takes it. -/
def anyAt (s : String) (i : Nat) :
    Except Failure (Char × { j : Nat // i < j ∧ i < s.utf8ByteSize }) :=
  if h : i < s.utf8ByteSize then
    .ok (String.Pos.Raw.get s ⟨i⟩, ⟨(String.Pos.Raw.next s ⟨i⟩).byteIdx,
      String.Pos.Raw.byteIdx_lt_byteIdx_next s ⟨i⟩, h⟩)
  else .error ⟨i, endOfInput⟩

/-- The first offset from `i` that holds no JSON white space. -/
def skipWs (s : String) (i : Nat) : { j : Nat // i ≤ j } :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ (String.Pos.Raw.lt_iff.mpr h)
    if b == 9 || b == 10 || b == 13 || b == 32 then
      let ⟨j, hj⟩ := skipWs s (i + 1)
      ⟨j, by omega⟩
    else ⟨i, Nat.le_refl _⟩
  else ⟨i, Nat.le_refl _⟩
termination_by s.utf8ByteSize - i

/-- A hexadecimal digit's value, as Lean's parser's `hexChar` reads one. -/
def hexAt (s : String) (i : Nat) : Except Failure (UInt16 × { j : Nat // i < j }) :=
  match anyAt s i with
  | .error f => .error f
  | .ok (c, ⟨j, hj⟩) =>
    match Hex.digit? c with
    | some d => .ok (d.toUInt16, ⟨j, hj.1⟩)
    | none => .error ⟨j, "invalid hex character"⟩

/-- `n` hexadecimal digits from `i` as one code unit, most significant first. -/
def hexUnit (s : String) (i : Nat) : Nat → UInt16 → Except Failure (UInt16 × { j : Nat // i ≤ j })
  | 0, acc => .ok (acc, ⟨i, Nat.le_refl _⟩)
  | n + 1, acc =>
    match hexAt s i with
    | .error f => .error f
    | .ok (d, ⟨j, hj⟩) =>
      match hexUnit s j n ((acc <<< 4) ||| d) with
      | .error f => .error f
      | .ok (u, ⟨k, hk⟩) => .ok (u, ⟨k, by omega⟩)

/-- The character a high surrogate `high` and the low surrogate escape from `i` stand for, and the
offset after it, as Lean's parser's `finishSurrogatePair` reads them. -/
def lowSurrogate (s : String) (i : Nat) (high : UInt16) : Option (Char × { j : Nat // i ≤ j }) :=
  match anyAt s i with
  | .ok ('\\', ⟨i1, h1⟩) =>
    match anyAt s i1 with
    | .ok ('u', ⟨i2, h2⟩) =>
      match anyAt s i2 with
      | .ok (d, ⟨i3, h3⟩) =>
        if d == 'd' || d == 'D' then
          match hexUnit s i3 3 0 with
          | .ok (val, ⟨i4, h4⟩) =>
            if val < 0xC00 then none
            else
              let code := (((high.toUInt32 &&& 0x3FF) <<< 10) ||| (val.toUInt32 &&& 0x3FF)) + 0x10000
              if h : code.isValidChar then some (⟨code, h⟩, ⟨i4, by omega⟩) else none
          | .error _ => none
        else none
      | _ => none
    | _ => none
  | _ => none

/-- The character an escape stands for, read after its backslash, and the offset after it, as
Lean's parser's `escapedChar` reads it. -/
def escapeAt (s : String) (i : Nat) : Except Failure (Char × { j : Nat // i < j }) :=
  match anyAt s i with
  | .error f => .error f
  | .ok (c, ⟨j, hj⟩) =>
    let one (x : Char) : Except Failure (Char × { j : Nat // i < j }) := .ok (x, ⟨j, hj.1⟩)
    match c with
    | '\\' => one '\\'
    | '"' => one '"'
    | '/' => one '/'
    | 'b' => one '\x08'
    | 'f' => one '\x0c'
    | 'n' => one '\n'
    | 'r' => one '\x0d'
    | 't' => one '\t'
    | 'u' =>
      match hexUnit s j 4 0 with
      | .error f => .error f
      | .ok (val, ⟨k, hk⟩) =>
        if h : val < 0xD800 then .ok (⟨val.toUInt32, Or.inl h⟩, ⟨k, by omega⟩)
        else if h' : val < 0xE000 then
          if val < 0xDC00 then
            match lowSurrogate s k val with
            | some (c, ⟨m, hm⟩) => .ok (c, ⟨m, by omega⟩)
            | none => .ok ('\uFFFD', ⟨k, by omega⟩)
          else .ok ('\uFFFD', ⟨k, by omega⟩)
        else .ok (⟨val.toUInt32, Or.inr ⟨Nat.not_lt.mp h',
          Nat.lt_trans val.toFin.isLt (by decide)⟩⟩, ⟨k, by omega⟩)
    | _ => .error ⟨j, "illegal \\u escape"⟩

/-- A string literal's characters onto `acc`, read after its opening quote, and the offset after its
closing quote, as Lean's parser's `strCore` reads them. -/
def strFrom (s : String) (i : Nat) (acc : String) : Except Failure (String × { j : Nat // i < j }) :=
  match byteAt? s i with
  | none => .error ⟨i, endOfInput⟩
  | some 34 => .ok (acc, ⟨i + 1, by omega⟩)
  | some _ =>
    match anyAt s i with
    | .error f => .error f
    | .ok (c, ⟨j, hj⟩) =>
      if c == '\\' then
        match escapeAt s j with
        | .error f => .error f
        | .ok (e, ⟨k, hk⟩) =>
          match strFrom s k (acc.push e) with
          | .error f => .error f
          | .ok (out, ⟨m, hm⟩) => .ok (out, ⟨m, by omega⟩)
      else if 0x20 ≤ c.val then
        match strFrom s j (acc.push c) with
        | .error f => .error f
        | .ok (out, ⟨m, hm⟩) => .ok (out, ⟨m, by omega⟩)
      else .error ⟨j, "unexpected character in string"⟩
termination_by s.utf8ByteSize - i
decreasing_by all_goals omega

/-- Decimal digits from `i` onto `acc`, with their count onto `count`, and the offset after them. -/
def digitsFrom (s : String) (i acc count : Nat) : Nat × Nat × { j : Nat // i ≤ j } :=
  match hb : byteAt? s i with
  | some b =>
    if 48 ≤ b && b ≤ 57 then
      have : i < s.utf8ByteSize := by
        unfold byteAt? at hb; split at hb
        · assumption
        · exact absurd hb (by simp)
      let (v, n, ⟨j, hj⟩) := digitsFrom s (i + 1) (10 * acc + (b.toNat - 48)) (count + 1)
      (v, n, ⟨j, by omega⟩)
    else (acc, count, ⟨i, Nat.le_refl _⟩)
  | none => (acc, count, ⟨i, Nat.le_refl _⟩)
termination_by s.utf8ByteSize - i

/-- Whether the byte at `i` is a decimal digit, failing as Lean's parser's `lookahead` fails. -/
def digitAhead (s : String) (i : Nat) (lo : UInt8) (desc : String) : Except Failure Unit :=
  match byteAt? s i with
  | none => .error ⟨i, endOfInput⟩
  | some b => if lo ≤ b && b ≤ 57 then .ok () else .error ⟨i, "expected " ++ desc⟩

/-- The largest positive exponent a number is read with: its power of ten is built, which past this
grows without bound where Lean's reader would build it or abort. -/
public def maxShift : Nat := 4096

/-- A number from `i`, its first byte a sign or a digit, and the offset after it, as Lean's
parser's `num` reads it. -/
def numFrom (s : String) (i : Nat) : Except Failure (JsonNumber × { j : Nat // i < j }) := do
  let (sign, i1) : Int × Nat := if byteAt? s i == some 45 then (-1, i + 1) else (1, i)
  let (whole, i2) ← match byteAt? s i1 with
    | none => .error ⟨i1, endOfInput⟩
    | some 48 => pure (0, i1 + 1)
    | some _ => do
      digitAhead s i1 49 "1-9"
      let (v, _, ⟨j, _⟩) := digitsFrom s i1 0 0
      pure (v, j)
  let (value, i3) ← match byteAt? s i2 with
    | some 46 => do
      digitAhead s (i2 + 1) 48 "digit"
      let (n, d, ⟨j, _⟩) := digitsFrom s (i2 + 1) 0 0
      if d > USize.size then .error ⟨j, "too many decimals"⟩
      pure (({ mantissa := sign * (whole * (10 ^ d : Nat) + n), exponent := d } : JsonNumber), j)
    | _ => pure (({ mantissa := sign * whole, exponent := 0 } : JsonNumber), i2)
  let (value, i4) ← match byteAt? s i3 with
    | some 101 | some 69 =>
      match byteAt? s (i3 + 1) with
      | none => .error ⟨i3 + 1, endOfInput⟩
      | some 45 => do
        digitAhead s (i3 + 2) 48 "0-9"
        let (n, _, ⟨j, _⟩) := digitsFrom s (i3 + 2) 0 0
        pure (value.shiftr n, j)
      | some b => do
        let k := if b == 43 then i3 + 2 else i3 + 1
        digitAhead s k 48 "0-9"
        let (n, _, ⟨j, _⟩) := digitsFrom s k 0 0
        if n > maxShift then .error ⟨j, "exp too large"⟩
        pure (value.shiftl n, j)
    | _ => pure (value, i3)
  if h : i < i4 then pure (value, ⟨i4, h⟩) else .error ⟨i4, endOfInput⟩

/-- Whether the text at `i` spells `word`, which is ASCII. -/
def spells (s : String) (i : Nat) (word : String) : Bool :=
  (List.range word.utf8ByteSize).all fun k => byteAt? s (i + k) == byteAt? word k

/-- An object's key and colon from `i`, and the offset of its value, as Lean's parser's
`objectCore` reads them. -/
def keyFrom (s : String) (i : Nat) : Except Failure (String × { j : Nat // i < j }) :=
  match byteAt? s i with
  | none => .error ⟨i, endOfInput⟩
  | some 34 =>
    match strFrom s (i + 1) "" with
    | .error f => .error f
    | .ok (k, ⟨j, hj⟩) =>
      let ⟨j, hw⟩ := skipWs s j
      match byteAt? s j with
      | none => .error ⟨j, endOfInput⟩
      | some 58 =>
        let ⟨m, hm⟩ := skipWs s (j + 1)
        .ok (k, ⟨m, by omega⟩)
      | some _ => .error ⟨j, "expected :"⟩
  | some _ => .error ⟨i, "expected \""⟩

/-- A container a value is read into: an array's elements so far, or an object's members so far
and the key whose value comes next. -/
inductive Frame where
  | arr (elems : Array Json)
  | obj (members : Array (String × Json)) (key : String)

/-- The value from `i` on, white space before it skipped, with `stack` the containers it closes
into and `done` a finished value awaiting its container's next character: the outermost value and
the offset after it and its trailing white space, as Lean's parser's `anyCore` reads them. -/
def run (s : String) (stack : List Frame) (i : Nat) (done : Option Json) :
    Except Failure (Json × Nat) :=
  match done with
  | some v =>
    match stack with
    | [] => .ok (v, i)
    | .arr elems :: rest =>
      match anyAt s i with
      | .error f => .error f
      | .ok (c, ⟨j, _hj⟩) =>
        let ⟨k, _hk⟩ := skipWs s j
        if c == ']' then run s rest k (some (.arr (elems.push v)))
        else if c == ',' then run s (.arr (elems.push v) :: rest) k none
        else .error ⟨j, "unexpected character in array"⟩
    | .obj members key :: rest =>
      match anyAt s i with
      | .error f => .error f
      | .ok (c, ⟨j, _hj⟩) =>
        let ⟨k, _hk⟩ := skipWs s j
        if c == '}' then run s rest k (some (.obj (settle (members.push (key, v)))))
        else if c == ',' then
          match keyFrom s k with
          | .error f => .error f
          | .ok (key', ⟨m, _hm⟩) => run s (.obj (members.push (key, v)) key' :: rest) m none
        else .error ⟨j, "unexpected character in object"⟩
  | none =>
    match hb : byteAt? s i with
    | none => .error ⟨i, endOfInput⟩
    | some b =>
      have _hi : i < s.utf8ByteSize := by
        unfold byteAt? at hb; split at hb
        · assumption
        · exact absurd hb (by simp)
      if b == 91 then
        let ⟨j, _hj⟩ := skipWs s (i + 1)
        match byteAt? s j with
        | none => .error ⟨j, endOfInput⟩
        | some 93 =>
          let ⟨k, _hk⟩ := skipWs s (j + 1)
          run s stack k (some (.arr #[]))
        | some _ => run s (.arr #[] :: stack) j none
      else if b == 123 then
        let ⟨j, _hj⟩ := skipWs s (i + 1)
        match byteAt? s j with
        | none => .error ⟨j, endOfInput⟩
        | some 125 =>
          let ⟨k, _hk⟩ := skipWs s (j + 1)
          run s stack k (some (.obj #[]))
        | some _ =>
          match keyFrom s j with
          | .error f => .error f
          | .ok (key, ⟨m, _hm⟩) => run s (.obj #[] key :: stack) m none
      else if b == 34 then
        match strFrom s (i + 1) "" with
        | .error f => .error f
        | .ok (text, ⟨j, _hj⟩) =>
          let ⟨k, _hk⟩ := skipWs s j
          run s stack k (some (.str text))
      else if b == 102 then
        if spells s i "false" then
          let ⟨k, _hk⟩ := skipWs s (i + 5)
          run s stack k (some (.bool false))
        else .error ⟨i, "expected: false"⟩
      else if b == 116 then
        if spells s i "true" then
          let ⟨k, _hk⟩ := skipWs s (i + 4)
          run s stack k (some (.bool true))
        else .error ⟨i, "expected: true"⟩
      else if b == 110 then
        if spells s i "null" then
          let ⟨k, _hk⟩ := skipWs s (i + 4)
          run s stack k (some .null)
        else .error ⟨i, "expected: null"⟩
      else if b == 45 || (48 ≤ b && b ≤ 57) then
        match numFrom s i with
        | .error f => .error f
        | .ok (n, ⟨j, _hj⟩) =>
          let ⟨k, _hk⟩ := skipWs s j
          run s stack k (some (.num n))
      else .error ⟨i, "unexpected input"⟩
termination_by s.utf8ByteSize - i
decreasing_by all_goals omega

/-- The text as one JSON value, or the failure Lean's `Json.parse` names. -/
public def parse (s : String) : Except String Json :=
  match run s [] (skipWs s 0).1 none with
  | .error f => .error s!"offset {f.pos}: {f.msg}"
  | .ok (v, i) => if i < s.utf8ByteSize then .error s!"offset {i}: expected end of input" else .ok v

/-! Lookup. -/

/-- An array's elements. -/
public def getArr? : Json → Except String (Array Json)
  | .arr a => .ok a
  | _ => .error "array expected"

/-- A string's text. -/
public def getStr? : Json → Except String String
  | .str s => .ok s
  | _ => .error "String expected"

/-- An object member's value. -/
public def getObjVal? : Json → String → Except String Json
  | .obj kvs, k =>
    match kvs.find? (·.1 == k) with
    | some (_, v) => .ok v
    | none => .error s!"property not found: {k}"
  | _, _ => .error "object expected"

/-- An object member's value, or `null`. -/
public def getObjValD (j : Json) (k : String) : Json :=
  match j.getObjVal? k with
  | .ok v => v
  | .error _ => .null

/-- A type a value reads as, as Lean's `FromJson` instances read it. -/
public class Read (α : Type) where
  read : Json → Except String α

public instance : Read Json := ⟨.ok⟩

public instance : Read Nat where
  read
    | .num ⟨.ofNat n, 0⟩ => .ok n
    | _ => .error "Natural number expected"

public instance : Read String := ⟨getStr?⟩

public instance : Read Bool where
  read
    | .bool b => .ok b
    | _ => .error "Bool expected"

public instance : Read (Array Json) where
  read
    | .arr a => .ok a
    | j => .error s!"expected JSON array, got '{j.pretty}'"

/-- An object member's value read as `α`, a missing one read as `null`. -/
public def getObjValAs? (j : Json) (α : Type) [Read α] (k : String) : Except String α :=
  Read.read (j.getObjValD k)

end Json

end LeanTex.Core.JsonText
