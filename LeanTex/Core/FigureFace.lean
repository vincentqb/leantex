module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Binary
public import LeanTex.Core.Flate

/-!
# A figure's web face, as the face cache keeps it

What deciding a PDF figure's web face reads of its import: the losses the
import named, the engine's drawing and the words it says, or why the import
refused the page. The import is a pure function of the page's bytes, so its
answer is kept under them — a refusal as much as a drawing — beside the key
it answers (the bytes' content key, the page, the stretch and the engine
that read them), and read back as itself under that key and as nothing
under any other (`lookup_exact`); bytes that do not check against their own
checksum are a miss, never another face.
-/

namespace LeanTex.Core.FigureFace

open LeanTex.Core

/-- An import's drawing as a face's decision reads it: the losses it named,
the engine's SVG of it, and the words it says (`Gfx.Figure.said`) — the text
its PDF form carries. -/
public structure Drawing where
  losses : Array Gfx.Loss
  face : ByteArray
  words : String
  deriving Inhabited

/-- What a face's decision reads of an import: its drawing, or why it
refused. -/
public abbrev Answer := Except String Drawing

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

/-- An answer's record: tag 0 and a refusal's words, or tag 1, the losses
(their count, then each), the drawing (its size, then its bytes) and its
words. -/
@[expose] public def answerBytes : Answer → ByteArray
  | .error why =>
    let words := Binary.str why
    Binary.natBE 1 0 ++ words
  | .ok d =>
    Binary.natBE 1 1 ++ Binary.natBE 4 d.losses.size ++ Binary.array encodeLoss d.losses ++
      Binary.natBE 4 d.face.size ++ d.face ++ Binary.str d.words

/-- The second step of reading an answer, by its tag. -/
public def readTagged (tag : Nat) : Binary.Reader Answer :=
  if tag == 0 then do
    let why ← Binary.Reader.str
    return .error why
  else if tag == 1 then do
    let n ← Binary.Reader.nat 4
    let losses ← Binary.Reader.many readLoss n #[]
    let size ← Binary.Reader.nat 4
    let face ← Binary.Reader.bytes size
    let words ← Binary.Reader.str
    return .ok { losses, face, words }
  else Binary.Reader.lift none

public def readAnswer : Binary.Reader Answer := do
  let tag ← Binary.Reader.nat 1
  readTagged tag

/-- A slot's body: the key its answer answers — its parts' count, then each
— and the answer. -/
@[expose] public def body (key : Array String) (a : Answer) : ByteArray :=
  let answer := answerBytes a
  Binary.natBE 4 key.size ++ Binary.array Binary.str key ++ answer

public def readBody : Binary.Reader (Array String × Answer) := do
  let n ← Binary.Reader.nat 4
  let key ← Binary.Reader.many Binary.Reader.str n #[]
  let a ← readAnswer
  return (key, a)

/-- The file's first bytes. -/
@[expose] public def magic : ByteArray := "LTFACE2\n".toUTF8

/-- A body's checksum (FNV-64, `Flate.fnv64`). -/
@[expose] public def checksum (b : ByteArray) : Nat := (Flate.fnv64 14695981039346656037 b).toNat

/-- **An answer as the cache stores it**, under the key it answers: the
magic, the body's checksum and size, the body. -/
@[expose] public def encode (key : Array String) (a : Answer) : ByteArray :=
  let b := body key a
  magic ++ Binary.natBE 8 (checksum b) ++ Binary.natBE 4 b.size ++ b

/-- The last step of reading a file: the body, where its checksum holds. -/
public def checked (ck : Nat) (b : ByteArray) : Option (Array String × Answer) :=
  if checksum b == ck then readBody.run b else none

public def readAll : Binary.Reader (Array String × Answer) := do
  Binary.Reader.expect magic
  let ck ← Binary.Reader.nat 8
  let n ← Binary.Reader.nat 4
  let b ← Binary.Reader.bytes n
  Binary.Reader.lift (checked ck b)

/-- A stored answer read back with its key; `none` for anything else — a
truncated, corrupted or foreign file is a miss. -/
public def decode (bytes : ByteArray) : Option (Array String × Answer) := readAll.run bytes

/-- **A slot read for a key**: the answer it holds where it was stored
under that very key, else a miss — a slot another engine, page, stretch or
file wrote answers nothing here, whatever its name. -/
public def lookup (key : Array String) (bytes : ByteArray) : Option Answer :=
  (decode bytes).bind fun (k, a) => if k == key then some a else none

/-- What an answer's own record needs to fit the format: every length it
stores fits 32 bits. -/
@[expose] public def AnswerBounded : Answer → Prop
  | .error why => why.toUTF8.size < 256 ^ 4
  | .ok d =>
    d.losses.size < 256 ^ 4 ∧ d.face.size < 256 ^ 4 ∧ d.words.toUTF8.size < 256 ^ 4 ∧
      ∀ l ∈ d.losses, (lossName l).toUTF8.size < 256 ^ 4

/-- An answer the format holds under a key: every length it stores fits 32
bits. -/
@[expose] public def Bounded (key : Array String) (a : Answer) : Prop :=
  (body key a).size < 256 ^ 4 ∧ key.size < 256 ^ 4 ∧ (∀ s ∈ key, s.toUTF8.size < 256 ^ 4) ∧
    AnswerBounded a

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

private theorem reads_answer (a : Answer) (h : AnswerBounded a) :
    Binary.Reads readAnswer a (answerBytes a) := by
  unfold readAnswer
  cases a with
  | error why =>
    have hp := Binary.Reads.bind Binary.Reader.str (fun why => (pure (Except.error why) : Binary.Reader Answer))
      why (.error why) (Binary.str why) .empty (Binary.Reads.str _ h) (Binary.Reads.pure _)
    rw [ByteArray.append_empty] at hp
    have ht : Binary.Reads (readTagged 0) (.error why) (Binary.str why) := by
      unfold readTagged
      simpa using hp
    exact Binary.Reads.bind (Binary.Reader.nat 1) readTagged 0 (.error why) (Binary.natBE 1 0)
      (Binary.str why) (Binary.Reads.nat 1 0 (by decide)) ht
  | ok d =>
    obtain ⟨losses, face, words⟩ := d
    obtain ⟨hn, hf, hw, hl⟩ := h
    have hwords := Binary.Reads.bind Binary.Reader.str
      (fun words => (pure (Except.ok { losses, face, words }) : Binary.Reader Answer))
      words (Except.ok { losses, face, words } : Answer) (Binary.str words) .empty
      (Binary.Reads.str _ hw) (Binary.Reads.pure _)
    rw [ByteArray.append_empty] at hwords
    have hface := Binary.Reads.bind (Binary.Reader.bytes face.size)
      (fun face => Binary.Reader.str >>= fun words =>
        (pure (Except.ok { losses, face, words }) : Binary.Reader Answer))
      face (Except.ok { losses, face, words } : Answer) face (Binary.str words)
      (Binary.Reads.bytes face) hwords
    have hsize := Binary.Reads.bind (Binary.Reader.nat 4)
      (fun size => Binary.Reader.bytes size >>= fun face => Binary.Reader.str >>= fun words =>
        (pure (Except.ok { losses, face, words }) : Binary.Reader Answer))
      face.size (Except.ok { losses, face, words } : Answer)
      (Binary.natBE 4 face.size) (face ++ Binary.str words) (Binary.Reads.nat 4 _ hf) hface
    have hmany := Binary.Reads.many readLoss encodeLoss losses.toList #[]
      (fun l hm => reads_loss l (hl l (by simpa using hm)))
    simp only [Array.empty_append, Array.toArray_toList,
      Array.length_toList] at hmany
    have hlosses := Binary.Reads.bind (Binary.Reader.many readLoss losses.size #[])
      (fun losses => do
        let size ← Binary.Reader.nat 4
        let face ← Binary.Reader.bytes size
        let words ← Binary.Reader.str
        return (Except.ok { losses, face, words } : Answer))
      losses (Except.ok { losses, face, words } : Answer) (Binary.array encodeLoss losses)
      (Binary.natBE 4 face.size ++ (face ++ Binary.str words)) hmany hsize
    have hcount := Binary.Reads.bind (Binary.Reader.nat 4)
      (fun n => Binary.Reader.many readLoss n #[] >>= fun losses => do
        let size ← Binary.Reader.nat 4
        let face ← Binary.Reader.bytes size
        let words ← Binary.Reader.str
        return (Except.ok { losses, face, words } : Answer))
      losses.size (Except.ok { losses, face, words } : Answer)
      (Binary.natBE 4 losses.size) _ (Binary.Reads.nat 4 _ hn) hlosses
    have ht : Binary.Reads (readTagged 1) (Except.ok { losses, face, words } : Answer)
        (Binary.natBE 4 losses.size ++ (Binary.array encodeLoss losses ++
          (Binary.natBE 4 face.size ++ (face ++ Binary.str words)))) := by
      unfold readTagged
      simpa using hcount
    have := Binary.Reads.bind (Binary.Reader.nat 1) readTagged 1
      (Except.ok { losses, face, words } : Answer) (Binary.natBE 1 1)
      _ (Binary.Reads.nat 1 1 (by decide)) ht
    simpa only [answerBytes, ByteArray.append_assoc] using this

private theorem reads_body (key : Array String) (a : Answer) (h : Bounded key a) :
    Binary.Reads readBody (key, a) (body key a) := by
  obtain ⟨_, hk, hks, ha⟩ := h
  have hans := reads_answer a ha
  unfold readBody body
  have hret := Binary.Reads.bind readAnswer
    (fun a => (pure (key, a) : Binary.Reader (Array String × Answer)))
    a (key, a) (answerBytes a) .empty hans (Binary.Reads.pure _)
  rw [ByteArray.append_empty] at hret
  have hmany := Binary.Reads.many Binary.Reader.str Binary.str key.toList #[]
    (fun s hm => Binary.Reads.str s (hks s (by simpa using hm)))
  simp only [Array.empty_append, Array.toArray_toList, Array.length_toList] at hmany
  have hkey := Binary.Reads.bind (Binary.Reader.many Binary.Reader.str key.size #[])
    (fun key => readAnswer >>= fun a => (pure (key, a) : Binary.Reader (Array String × Answer)))
    key (key, a) (Binary.array Binary.str key) (answerBytes a) hmany hret
  have := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.many Binary.Reader.str n #[] >>= fun key => readAnswer >>= fun a =>
      (pure (key, a) : Binary.Reader (Array String × Answer)))
    key.size (key, a) (Binary.natBE 4 key.size) _ (Binary.Reads.nat 4 _ hk) hkey
  simpa only [ByteArray.append_assoc] using this

/-- **A stored answer reads back as itself, with its key** (`_id`): every
answer the format holds — a refusal's words, a drawing's losses, bytes and
words, empty ones included — under every key it holds. -/
public theorem decode_encode_id (key : Array String) (a : Answer) (h : Bounded key a) :
    decode (encode key a) = some (key, a) := by
  unfold decode
  apply Binary.Reads.run_id
  unfold readAll encode
  have hrun : readBody.run (body key a) = some (key, a) :=
    Binary.Reads.run_id readBody (key, a) (body key a) (reads_body key a h)
  have hlift : Binary.Reads (Binary.Reader.lift (checked (checksum (body key a)) (body key a))) (key, a) .empty :=
    Binary.Reads.lift _ (key, a) (by simp [checked, hrun])
  have hb := Binary.Reads.bind (Binary.Reader.bytes (body key a).size)
    (fun b => Binary.Reader.lift (checked (checksum (body key a)) b)) (body key a) (key, a) (body key a) .empty
    (Binary.Reads.bytes _) hlift
  rw [ByteArray.append_empty] at hb
  have hn := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.bytes n >>= fun b => Binary.Reader.lift (checked (checksum (body key a)) b))
    (body key a).size (key, a) (Binary.natBE 4 (body key a).size) (body key a) (Binary.Reads.nat 4 _ h.1) hb
  have hck := Binary.Reads.bind (Binary.Reader.nat 8)
    (fun ck => Binary.Reader.nat 4 >>= fun n => Binary.Reader.bytes n >>= fun b =>
      Binary.Reader.lift (checked ck b))
    (checksum (body key a)) (key, a) (Binary.natBE 8 (checksum (body key a))) _
    (Binary.Reads.nat 8 _ (by
      have := (Flate.fnv64 14695981039346656037 (body key a)).toNat_lt
      simpa [checksum] using this)) hn
  have := Binary.Reads.bind (Binary.Reader.expect magic)
    (fun _ => Binary.Reader.nat 8 >>= fun ck => Binary.Reader.nat 4 >>= fun n =>
      Binary.Reader.bytes n >>= fun b => Binary.Reader.lift (checked ck b))
    () (key, a) magic _ (Binary.Reads.expect magic) hck
  simpa only [ByteArray.append_assoc] using this

/-- **A slot answers its own key and no other** (`_exact`): an answer
stored under a key reads back as itself for that key, and as a miss for
every other — the key, not the slot's file name, is what a hit rests on, so
a slot written by another engine, for another page or stretch, or for other
bytes whose name collides, is read afresh and never served. -/
public theorem lookup_exact (key : Array String) (a : Answer) (h : Bounded key a) :
    lookup key (encode key a) = some a ∧ ∀ key', key' ≠ key → lookup key' (encode key a) = none := by
  have hd := decode_encode_id key a h
  refine ⟨by simp [lookup, hd], fun key' hne => ?_⟩
  simp only [lookup, hd, Option.bind_some]
  exact ite_eq_right_iff.mpr fun e => absurd (beq_iff_eq.mp e).symm hne

end LeanTex.Core.FigureFace
