import LeanTex.Core.Diag

namespace LeanTex.Core.Utf8

inductive ErrKind where
  | invalidStart (b : UInt8)
  | invalidContinuation (b : UInt8)
  | truncated
  | overlong
  | surrogate
  | outOfRange
  deriving Repr, BEq

def ErrKind.message : ErrKind → String
  | .invalidStart b => s!"invalid start byte 0x{hex b}"
  | .invalidContinuation b => s!"invalid continuation byte 0x{hex b}"
  | .truncated => "truncated multi-byte sequence"
  | .overlong => "overlong encoding"
  | .surrogate => "surrogate code point"
  | .outOfRange => "code point beyond U+10FFFF"
where
  hex (b : UInt8) : String :=
    let digit (n : UInt8) : Char := "0123456789ABCDEF".toList[n.toNat]!
    String.ofList [digit (b >>> 4), digit (b &&& 0xF)]

structure Err where
  offset : Nat
  pos : Pos
  kind : ErrKind
  deriving Repr, BEq

def Err.toDiag (e : Err) (file : String) : Diag :=
  Diag.of .E0002 s!"invalid UTF-8: {e.kind.message} at byte offset {e.offset}"
    (some ⟨file, e.pos⟩)
    (help := "every input is read as UTF-8; `iconv -t utf-8` re-encodes the file")

private def isCont (b : UInt8) : Bool := b &&& 0xC0 == 0x80

/-- Width and validity of the sequence starting at `i`; `bs[i]` is a valid
start byte for `width` total bytes, all bounds already known in range. -/
private def seq (bs : ByteArray) (i : Nat) : Except ErrKind Nat := do
  let b0 := bs[i]!
  if b0 < 0x80 then return 1
  else if b0 < 0xC0 then throw (.invalidStart b0)
  else if b0 < 0xC2 then throw .overlong
  else if b0 < 0xE0 then check 1 (fun _ => .ok ()) *> return 2
  else if b0 < 0xF0 then
    check 2 (fun b1 =>
      if b0 == 0xE0 && b1 < 0xA0 then throw .overlong
      else if b0 == 0xED && b1 >= 0xA0 then throw .surrogate
      else .ok ()) *> return 3
  else if b0 < 0xF5 then
    check 3 (fun b1 =>
      if b0 == 0xF0 && b1 < 0x90 then throw .overlong
      else if b0 == 0xF4 && b1 >= 0x90 then throw .outOfRange
      else .ok ()) *> return 4
  else throw (.invalidStart b0)
where
  check (n : Nat) (first : UInt8 → Except ErrKind Unit) : Except ErrKind Unit := do
    for k in [1:n+1] do
      if i + k >= bs.size then throw .truncated
      let b := bs[i + k]!
      if !isCont b then throw (.invalidContinuation b)
      if k == 1 then first b

/-- First UTF-8 error in `bs`, with byte offset and line/column, or `none`
when the bytes are valid. Terminating (not fueled): each step advances by
`max 1 width`, and `seq` only ever returns 1–4, so the `max` is a no-op that
makes the decrease visible to the checker. -/
def validate (bs : ByteArray) : Option Err :=
  go 0 {}
where
  go (i : Nat) (pos : Pos) : Option Err :=
    if i ≥ bs.size then
      none
    else
      match seq bs i with
      | .error kind => some ⟨i, pos, kind⟩
      | .ok width =>
        go (i + max 1 width) (pos.next (bs[i]! == 0x0A))
  termination_by bs.size - i
  decreasing_by
    simp_wf
    omega

end LeanTex.Core.Utf8
