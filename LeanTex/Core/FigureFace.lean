module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Binary
public import LeanTex.Core.Flate

/-!
# A figure's web face, as the face cache keeps it

What deciding a PDF figure's web face reads of its import: the losses the
import named and the engine's drawing, or why the import refused the page.
The import is a pure function of the page's bytes, so its answer is kept
under them — a refusal as much as a drawing — and read back as itself
(`decode_encode_id`); bytes that do not check against their own checksum
are a miss, never another face.
-/

namespace LeanTex.Core.FigureFace

open LeanTex.Core

/-- What a face's decision reads of an import: its losses and drawing, or
why it refused. -/
public abbrev Answer := Except String (Array Gfx.Loss × ByteArray)

/-- A loss's kind, as a record's tag. -/
@[expose] public def lossTag : Gfx.Loss → Nat
  | .element _ => 0
  | .attribute _ => 1
  | .property _ => 2
  | .value _ => 3
  | .operator _ => 4
  | .resource _ => 5
  | .font _ => 6
  | .budget _ => 7

/-- A loss's name. -/
@[expose] public def lossName : Gfx.Loss → String
  | .element n | .attribute n | .property n | .value n | .operator n | .resource n
  | .font n | .budget n => n

/-- A loss from its record's tag and name. -/
@[expose] public def lossOf : Nat → String → Option Gfx.Loss
  | 0, n => some (.element n)
  | 1, n => some (.attribute n)
  | 2, n => some (.property n)
  | 3, n => some (.value n)
  | 4, n => some (.operator n)
  | 5, n => some (.resource n)
  | 6, n => some (.font n)
  | 7, n => some (.budget n)
  | _, _ => none

/-- A loss's record: its tag, then its name. -/
@[expose] public def encodeLoss (l : Gfx.Loss) : ByteArray :=
  Binary.natBE 1 (lossTag l) ++ Binary.str (lossName l)

public def readLoss : Binary.Reader Gfx.Loss := do
  let tag ← Binary.Reader.nat 1
  let name ← Binary.Reader.str
  Binary.Reader.lift (lossOf tag name)

/-- An answer's body: tag 0 and a refusal's words, or tag 1, the losses
(their count, then each), and the drawing (its size, then its bytes). -/
@[expose] public def body : Answer → ByteArray
  | .error why =>
    let words := Binary.str why
    Binary.natBE 1 0 ++ words
  | .ok (losses, face) =>
    Binary.natBE 1 1 ++ Binary.natBE 4 losses.size ++ Binary.array encodeLoss losses ++
      Binary.natBE 4 face.size ++ face

/-- The second step of reading a body, by its tag. -/
public def readTagged (tag : Nat) : Binary.Reader Answer :=
  if tag == 0 then do
    let why ← Binary.Reader.str
    return .error why
  else if tag == 1 then do
    let n ← Binary.Reader.nat 4
    let losses ← Binary.Reader.many readLoss n #[]
    let size ← Binary.Reader.nat 4
    let face ← Binary.Reader.bytes size
    return .ok (losses, face)
  else Binary.Reader.lift none

public def readBody : Binary.Reader Answer := do
  let tag ← Binary.Reader.nat 1
  readTagged tag

/-- The file's first bytes. -/
@[expose] public def magic : ByteArray := "LTFACE1\n".toUTF8

/-- A body's checksum (FNV-64, `Flate.fnv64`). -/
@[expose] public def checksum (b : ByteArray) : Nat := (Flate.fnv64 14695981039346656037 b).toNat

/-- **An answer as the cache stores it**: the magic, the body's checksum
and size, the body. -/
@[expose] public def encode (a : Answer) : ByteArray :=
  let b := body a
  magic ++ Binary.natBE 8 (checksum b) ++ Binary.natBE 4 b.size ++ b

/-- The last step of reading a file: the body, where its checksum holds. -/
public def checked (ck : Nat) (b : ByteArray) : Option Answer :=
  if checksum b == ck then readBody.run b else none

public def readAll : Binary.Reader Answer := do
  Binary.Reader.expect magic
  let ck ← Binary.Reader.nat 8
  let n ← Binary.Reader.nat 4
  let b ← Binary.Reader.bytes n
  Binary.Reader.lift (checked ck b)

/-- A stored answer read back; `none` for anything else — a truncated,
corrupted or foreign file is a miss. -/
public def decode (bytes : ByteArray) : Option Answer := readAll.run bytes

/-- An answer the format holds: every length it stores fits 32 bits. -/
@[expose] public def Bounded (a : Answer) : Prop :=
  (body a).size < 256 ^ 4 ∧
    match a with
    | .error why => why.toUTF8.size < 256 ^ 4
    | .ok (losses, face) =>
      losses.size < 256 ^ 4 ∧ face.size < 256 ^ 4 ∧ ∀ l ∈ losses, (lossName l).toUTF8.size < 256 ^ 4

private theorem reads_loss (l : Gfx.Loss) (h : (lossName l).toUTF8.size < 256 ^ 4) :
    Binary.Reads readLoss l (encodeLoss l) := by
  unfold readLoss encodeLoss
  have hl : Binary.Reads (Binary.Reader.lift (lossOf (lossTag l) (lossName l))) l .empty :=
    Binary.Reads.lift _ l (by cases l <;> rfl)
  have hs := Binary.Reads.bind Binary.Reader.str (fun name => Binary.Reader.lift (lossOf (lossTag l) name))
    (lossName l) l (Binary.str (lossName l)) .empty (Binary.Reads.str _ h) hl
  rw [ByteArray.append_empty] at hs
  exact Binary.Reads.bind (Binary.Reader.nat 1) _ (lossTag l) l (Binary.natBE 1 (lossTag l))
    (Binary.str (lossName l)) (Binary.Reads.nat 1 _ (by cases l <;> simp [lossTag])) hs

private theorem reads_body (a : Answer) (h : Bounded a) : Binary.Reads readBody a (body a) := by
  unfold readBody
  cases a with
  | error why =>
    have hb := h.2
    have hp := Binary.Reads.bind Binary.Reader.str (fun why => (pure (Except.error why) : Binary.Reader Answer))
      why (.error why) (Binary.str why) .empty (Binary.Reads.str _ hb) (Binary.Reads.pure _)
    rw [ByteArray.append_empty] at hp
    have ht : Binary.Reads (readTagged 0) (.error why) (Binary.str why) := by
      unfold readTagged
      simpa using hp
    exact Binary.Reads.bind (Binary.Reader.nat 1) readTagged 0 (.error why) (Binary.natBE 1 0)
      (Binary.str why) (Binary.Reads.nat 1 0 (by decide)) ht
  | ok p =>
    obtain ⟨losses, face⟩ := p
    obtain ⟨_, hn, hf, hl⟩ := h
    have hface := Binary.Reads.bind (Binary.Reader.bytes face.size)
      (fun face => (pure (Except.ok (losses, face)) : Binary.Reader Answer))
      face (Except.ok (losses, face) : Answer) face .empty (Binary.Reads.bytes face) (Binary.Reads.pure _)
    rw [ByteArray.append_empty] at hface
    have hsize := Binary.Reads.bind (Binary.Reader.nat 4)
      (fun size => Binary.Reader.bytes size >>= fun face =>
        (pure (Except.ok (losses, face)) : Binary.Reader Answer))
      face.size (Except.ok (losses, face) : Answer)
      (Binary.natBE 4 face.size) face (Binary.Reads.nat 4 _ hf) hface
    have hmany := Binary.Reads.many readLoss encodeLoss losses.toList #[]
      (fun l hm => reads_loss l (hl l (by simpa using hm)))
    simp only [Array.empty_append, Array.toArray_toList,
      Array.length_toList] at hmany
    have hlosses := Binary.Reads.bind (Binary.Reader.many readLoss losses.size #[])
      (fun losses => do
        let size ← Binary.Reader.nat 4
        let face ← Binary.Reader.bytes size
        return (Except.ok (losses, face) : Answer))
      losses (Except.ok (losses, face) : Answer) (Binary.array encodeLoss losses)
      (Binary.natBE 4 face.size ++ face) hmany hsize
    have hcount := Binary.Reads.bind (Binary.Reader.nat 4)
      (fun n => Binary.Reader.many readLoss n #[] >>= fun losses => do
        let size ← Binary.Reader.nat 4
        let face ← Binary.Reader.bytes size
        return (Except.ok (losses, face) : Answer))
      losses.size (Except.ok (losses, face) : Answer)
      (Binary.natBE 4 losses.size) _ (Binary.Reads.nat 4 _ hn) hlosses
    have ht : Binary.Reads (readTagged 1) (Except.ok (losses, face) : Answer)
        (Binary.natBE 4 losses.size ++ (Binary.array encodeLoss losses ++
          (Binary.natBE 4 face.size ++ face))) := by
      unfold readTagged
      simpa using hcount
    have := Binary.Reads.bind (Binary.Reader.nat 1) readTagged 1 (Except.ok (losses, face) : Answer) (Binary.natBE 1 1)
      _ (Binary.Reads.nat 1 1 (by decide)) ht
    simpa only [body, ByteArray.append_assoc] using this

/-- **A stored answer reads back as itself** (`_id`): every answer the
format holds — a refusal's words, a drawing's losses and bytes, empty ones
included. -/
public theorem decode_encode_id (a : Answer) (h : Bounded a) : decode (encode a) = some a := by
  unfold decode
  apply Binary.Reads.run_id
  unfold readAll encode
  have hrun : readBody.run (body a) = some a := Binary.Reads.run_id readBody a (body a) (reads_body a h)
  have hlift : Binary.Reads (Binary.Reader.lift (checked (checksum (body a)) (body a))) a .empty :=
    Binary.Reads.lift _ a (by simp [checked, hrun])
  have hb := Binary.Reads.bind (Binary.Reader.bytes (body a).size)
    (fun b => Binary.Reader.lift (checked (checksum (body a)) b)) (body a) a (body a) .empty
    (Binary.Reads.bytes _) hlift
  rw [ByteArray.append_empty] at hb
  have hn := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.bytes n >>= fun b => Binary.Reader.lift (checked (checksum (body a)) b))
    (body a).size a (Binary.natBE 4 (body a).size) (body a) (Binary.Reads.nat 4 _ h.1) hb
  have hck := Binary.Reads.bind (Binary.Reader.nat 8)
    (fun ck => Binary.Reader.nat 4 >>= fun n => Binary.Reader.bytes n >>= fun b =>
      Binary.Reader.lift (checked ck b))
    (checksum (body a)) a (Binary.natBE 8 (checksum (body a))) _
    (Binary.Reads.nat 8 _ (by
      have := (Flate.fnv64 14695981039346656037 (body a)).toNat_lt
      simpa [checksum] using this)) hn
  have := Binary.Reads.bind (Binary.Reader.expect magic)
    (fun _ => Binary.Reader.nat 8 >>= fun ck => Binary.Reader.nat 4 >>= fun n =>
      Binary.Reader.bytes n >>= fun b => Binary.Reader.lift (checked ck b))
    () a magic _ (Binary.Reads.expect magic) hck
  simpa only [ByteArray.append_assoc] using this

end LeanTex.Core.FigureFace
