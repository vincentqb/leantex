module

public import LeanTex.Core.Gfx
public import LeanTex.Core.KeyedRecord

/-! The face cache's record of a PDF figure's import, its drawing or its refusal, kept under the
key it answers. -/

namespace LeanTex.Core.FigureFace

open LeanTex.Core

/-- An import's drawing as a face's decision reads it: its losses, the engine's SVG, and its words. -/
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

/-- What an answer's own record needs to fit the format: every length it
stores fits 32 bits. -/
@[expose] public def AnswerBounded : Answer → Prop
  | .error why => why.toUTF8.size < 256 ^ 4
  | .ok d =>
    d.losses.size < 256 ^ 4 ∧ d.face.size < 256 ^ 4 ∧ d.words.toUTF8.size < 256 ^ 4 ∧
      ∀ l ∈ d.losses, (lossName l).toUTF8.size < 256 ^ 4

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

/-- A check that implies `AnswerBounded`. -/
@[expose] public def answerFits : Answer → Bool
  | .error why => decide (why.toUTF8.size < 256 ^ 4)
  | .ok d =>
    decide (d.losses.size < 256 ^ 4) && decide (d.face.size < 256 ^ 4) &&
      decide (d.words.toUTF8.size < 256 ^ 4) &&
        d.losses.all fun l => decide ((lossName l).toUTF8.size < 256 ^ 4)

private theorem answerFits_bounded (a : Answer) (h : answerFits a = true) : AnswerBounded a := by
  cases a with
  | error why => simpa [answerFits, AnswerBounded] using h
  | ok d =>
    simp only [answerFits, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
    obtain ⟨⟨⟨hn, hf⟩, hw⟩, hl⟩ := h
    refine ⟨hn, hf, hw, fun l hm => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hm
    simpa using hl i hi

/-- The face cache's format: its magic, and an answer's record. -/
@[expose] public def format : KeyedRecord.Format Answer where
  magic := "LTFACE2\n".toUTF8
  write := answerBytes
  read := readAnswer
  Fits := AnswerBounded
  reads := by exact reads_answer
  fits := answerFits
  fits_sound := by exact answerFits_bounded

/-- An answer as the cache stores it under its key. -/
@[expose] public def encode (key : Array String) (a : Answer) : ByteArray := KeyedRecord.encode format key a

/-- A slot read for a key: the answer stored under that very key, else a miss. -/
public def lookup (key : Array String) (bytes : ByteArray) : Option Answer :=
  KeyedRecord.lookup format key bytes

/-- An answer the format holds under a key: every length it stores fits 32 bits. -/
@[expose] public def Bounded (key : Array String) (a : Answer) : Prop :=
  KeyedRecord.Bounded format key a

/-- A check that implies `Bounded`, which the cache runs before it stores. -/
@[expose] public def storable (key : Array String) (a : Answer) : Bool :=
  KeyedRecord.storable format key a

public theorem storable_bounded (key : Array String) (a : Answer) (h : storable key a = true) :
    Bounded key a :=
  KeyedRecord.storable_bounded format key a h

public theorem lookup_exact (key : Array String) (a : Answer) (h : Bounded key a) :
    lookup key (encode key a) = some a ∧ ∀ key', key' ≠ key → lookup key' (encode key a) = none :=
  KeyedRecord.lookup_exact format key a h

end LeanTex.Core.FigureFace
