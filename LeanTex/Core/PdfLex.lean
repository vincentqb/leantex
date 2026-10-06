import Init.Data.ByteArray.Basic

namespace LeanTex.Core.PdfLex

/-! Byte-level PDF token rules shared by the object reader and its
round-trip contracts. Strings retain their original bytes. -/

def isWs (c : Nat) : Bool :=
  c == 0 || c == 9 || c == 10 || c == 12 || c == 13 || c == 32

def isDelim (c : Nat) : Bool :=
  c == 40 || c == 41 || c == 60 || c == 62 || c == 91 || c == 93 ||
  c == 123 || c == 125 || c == 47 || c == 37

def at? (b : ByteArray) (i : Nat) : Nat :=
  (b[i]?.map (·.toNat)).getD 256

def skipStep (b : ByteArray) (i : Nat) : ForInStep Nat := Id.run do
  let c := at? b i
  if isWs c then return .yield (i + 1)
  if c == 37 then
    let mut j := i
    for _ in [0:b.size + 1] do
      let d := at? b j
      if d == 10 || d == 13 || d == 256 then break
      j := j + 1
    return .yield j
  return .done i

/-- Skip whitespace and `%` comments (§7.2.3–4). -/
def skipWs (b : ByteArray) (i0 : Nat) : Nat :=
  (forIn [0:b.size + 1] i0 (fun _ i => pure (skipStep b i)) : Id Nat).run

structure UIntState where
  pos : Nat
  value : Nat
  seen : Bool

def uintStep (b : ByteArray) (s : UIntState) : ForInStep UIntState :=
  let c := at? b s.pos
  if 48 ≤ c && c ≤ 57 then
    .yield ⟨s.pos + 1, s.value * 10 + (c - 48), true⟩
  else .done s

/-- A run of digits as a `Nat`, or `none` when none stand at `i`. -/
def parseUInt (b : ByteArray) (i0 : Nat) : Option (Nat × Nat) :=
  let s := (forIn [0:b.size + 1] (UIntState.mk i0 0 false)
    (fun _ s => pure (uintStep b s)) : Id UIntState).run
  if s.seen then some (s.value, s.pos) else none

/-- A keyword comparison step. A mismatch ends the scan immediately. -/
def keywordStep (b : ByteArray) (i : Nat) (bytes : ByteArray) (k : Nat)
    (_ : Bool) : ForInStep Bool :=
  if at? b (i+k) == (bytes[k]?.getD 0).toNat then .yield true else .done false

/-- Does the keyword stand at `i`, ended by whitespace, a delimiter, or the
file's end? Returns the position after it. -/
def keywordAt (b : ByteArray) (i : Nat) (kw : String) : Option Nat :=
  let bytes := kw.toUTF8
  let matched := (forIn [0:bytes.size] true
    (fun k s => pure (keywordStep b i bytes k s)) : Id Bool).run
  let after := at? b (i+bytes.size)
  if matched && (after == 256 || isWs after || isDelim after) then
    some (i+bytes.size)
  else none

def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else none

structure LiteralState where
  pos : Nat
  depth : Nat
  result : Option Nat := none

def literalStep (b : ByteArray) (s : LiteralState) : ForInStep LiteralState :=
  let c := at? b s.pos
  if c == 256 then .done s
  else if c == 92 then .yield { s with pos := s.pos + 2 }
  else if c == 40 then .yield { s with pos := s.pos + 1, depth := s.depth + 1 }
  else if c == 41 then
    let next := { s with pos := s.pos + 1, depth := s.depth - 1 }
    if next.depth == 0 then .done { next with result := some next.pos }
    else .yield next
  else .yield { s with pos := s.pos + 1 }

/-- Scan a literal string `(…)` (§7.3.4.2): parentheses balance, and a
backslash escapes the next byte. Returns the position after the closing
parenthesis. -/
def scanLitString (b : ByteArray) (i0 : Nat) : Option Nat :=
  ((forIn [0:b.size + 1] (LiteralState.mk (i0+1) 1 none)
    (fun _ s => pure (literalStep b s)) : Id LiteralState).run).result

def hexStep (b : ByteArray) (i : Nat) : ForInStep Nat :=
  if at? b i == 62 || at? b i == 256 then .done i else .yield (i+1)

def scanHexEnd (b : ByteArray) (i : Nat) : Nat :=
  (forIn [0:b.size + 1] i (fun _ j => pure (hexStep b j)) : Id Nat).run

structure TextState where
  pos : Nat
  text : String

def nameStep (b : ByteArray) (s : TextState) : ForInStep TextState :=
  let c := at? b s.pos
  if c == 256 || isWs c || isDelim c then .done s
  else if c == 35 then
    match hexVal (at? b (s.pos + 1)), hexVal (at? b (s.pos + 2)) with
    | some h, some l => .yield ⟨s.pos + 3, s.text.push (Char.ofNat (h * 16 + l))⟩
    | _, _ => .yield ⟨s.pos + 1, s.text.push '#'⟩
  else .yield ⟨s.pos + 1, s.text.push (Char.ofNat c)⟩

/-- A name after its solidus (§7.3.5), `#`-escapes decoded. -/
def parseName (b : ByteArray) (i0 : Nat) : String × Nat :=
  let s := (forIn [0:b.size + 1] (TextState.mk (i0 + 1) "")
    (fun _ s => pure (nameStep b s)) : Id TextState).run
  (s.text, s.pos)

/-- The characters a number token is made of. -/
def numByte (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || c == 43 || c == 45 || c == 46

def numberStep (b : ByteArray) (s : TextState) : ForInStep TextState :=
  let c := at? b s.pos
  if numByte c then .yield ⟨s.pos + 1, s.text.push (Char.ofNat c)⟩
  else .done s

def scanNumber (b : ByteArray) (i0 : Nat) : String × Nat :=
  let s := (forIn [0:b.size + 1] (TextState.mk i0 "")
    (fun _ s => pure (numberStep b s)) : Id TextState).run
  (s.text, s.pos)

/-- After a non-negative integer, does ` gen R` follow (§7.3.10)? The
two-token lookahead an indirect reference needs. -/
def tryRef (b : ByteArray) (i0 : Nat) : Option (Nat × Nat) := do
  let (gen, j) ← parseUInt b (skipWs b i0)
  let k := skipWs b j
  if at? b k == 82 then  -- 'R'
    let after := at? b (k + 1)
    if after == 256 || isWs after || isDelim after then
      return (gen, k + 1)
  none

/-- A nibble as its uppercase hex digit — the spelling `#xx` escapes and
`parseName`'s `hexVal` read back. -/
def hexChar (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (55 + d)

/-- A name's byte escape (§7.3.5). The existing writer substitutes
`Embedded` for an empty name and keeps only the low byte of escaped
characters. Its inverse contract therefore requires a nonempty name with
character values below 256. -/
def escapeName (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c.isAlphanum || c == '-' || c == '.' then
      out := out.push c
    else
      out := out ++ "#" ++ String.ofList [hexChar (c.toNat / 16), hexChar c.toNat]
  return if out == "" then "Embedded" else out

end LeanTex.Core.PdfLex
