module

public import LeanTex.Core.Binary
public import LeanTex.Core.Flate

/-! A cache file that holds the key it answers: magic, checksum, size, then the key and the value,
read back as the value under that key, and as a miss under any other or when its checksum fails. -/

namespace LeanTex.Core.KeyedRecord

open LeanTex.Core

/-- A record kind: the file's first bytes, and its value's codec with the bound under which the
value reads back and a check that implies it. -/
public structure Format (α : Type) where
  magic : ByteArray
  write : α → ByteArray
  read : Binary.Reader α
  Fits : α → Prop
  reads : ∀ a, Fits a → Binary.Reads read a (write a)
  fits : α → Bool
  fits_sound : ∀ a, fits a = true → Fits a

variable {α : Type} (F : Format α)

/-- A record's body: the key its value answers — its parts' count, then each — and the value. -/
@[expose] public def body (key : Array String) (a : α) : ByteArray :=
  let value := F.write a
  Binary.natBE 4 key.size ++ Binary.array Binary.str key ++ value

public def readBody : Binary.Reader (Array String × α) := do
  let n ← Binary.Reader.nat 4
  let key ← Binary.Reader.many Binary.Reader.str n #[]
  let a ← F.read
  return (key, a)

/-- A body's FNV-64 checksum. -/
@[expose] public def checksum (b : ByteArray) : Nat := (Flate.fnv64 Flate.fnvOffset b).toNat

/-- A value as a cache stores it under its key: magic, the body's checksum and size, the body. -/
@[expose] public def encode (key : Array String) (a : α) : ByteArray :=
  let b := body F key a
  F.magic ++ Binary.natBE 8 (checksum b) ++ Binary.natBE 4 b.size ++ b

/-- The last step of reading a file: the body, where its checksum holds. -/
public def checked (ck : Nat) (b : ByteArray) : Option (Array String × α) :=
  if checksum b == ck then (readBody F).run b else none

public def readAll : Binary.Reader (Array String × α) := do
  Binary.Reader.expect F.magic
  let ck ← Binary.Reader.nat 8
  let n ← Binary.Reader.nat 4
  let b ← Binary.Reader.bytes n
  Binary.Reader.lift (checked F ck b)

/-- A stored value read back with its key; a truncated, corrupted or foreign file is `none`. -/
public def decode (bytes : ByteArray) : Option (Array String × α) := (readAll F).run bytes

/-- A record read for a key: the value stored under that very key, else a miss. -/
public def lookup (key : Array String) (bytes : ByteArray) : Option α :=
  (decode F bytes).bind fun (k, a) => if k == key then some a else none

/-- What a value needs to fit the format under a key: every length the record stores fits 32
bits. -/
@[expose] public def Bounded (key : Array String) (a : α) : Prop :=
  (body F key a).size < 256 ^ 4 ∧ key.size < 256 ^ 4 ∧ (∀ s ∈ key, s.toUTF8.size < 256 ^ 4) ∧
    F.Fits a

/-- A check that implies `Bounded`, which a cache runs before it stores. -/
@[expose] public def storable (key : Array String) (a : α) : Bool :=
  decide ((body F key a).size < 256 ^ 4) && decide (key.size < 256 ^ 4) &&
    key.all (fun s => decide (s.toUTF8.size < 256 ^ 4)) && F.fits a

public theorem storable_bounded (key : Array String) (a : α) (h : storable F key a = true) :
    Bounded F key a := by
  simp only [storable, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨hb, hk⟩, hs⟩, ha⟩ := h
  refine ⟨hb, hk, fun s hm => ?_, F.fits_sound a ha⟩
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hm
  simpa using hs i hi

private theorem reads_body (key : Array String) (a : α) (h : Bounded F key a) :
    Binary.Reads (readBody F) (key, a) (body F key a) := by
  obtain ⟨_, hk, hks, ha⟩ := h
  unfold readBody body
  have hret := Binary.Reads.bind F.read
    (fun a => (pure (key, a) : Binary.Reader (Array String × α)))
    a (key, a) (F.write a) .empty (F.reads a ha) (Binary.Reads.pure _)
  rw [ByteArray.append_empty] at hret
  have hmany := Binary.Reads.many Binary.Reader.str Binary.str key.toList #[]
    (fun s hm => Binary.Reads.str s (hks s (by simpa using hm)))
  simp only [Array.empty_append, Array.toArray_toList, Array.length_toList] at hmany
  have hkey := Binary.Reads.bind (Binary.Reader.many Binary.Reader.str key.size #[])
    (fun key => F.read >>= fun a => (pure (key, a) : Binary.Reader (Array String × α)))
    key (key, a) (Binary.array Binary.str key) (F.write a) hmany hret
  have := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.many Binary.Reader.str n #[] >>= fun key => F.read >>= fun a =>
      (pure (key, a) : Binary.Reader (Array String × α)))
    key.size (key, a) (Binary.natBE 4 key.size) _ (Binary.Reads.nat 4 _ hk) hkey
  simpa only [ByteArray.append_assoc] using this

public theorem decode_encode_id (key : Array String) (a : α) (h : Bounded F key a) :
    decode F (encode F key a) = some (key, a) := by
  unfold decode
  apply Binary.Reads.run_id
  unfold readAll encode
  have hrun : (readBody F).run (body F key a) = some (key, a) :=
    Binary.Reads.run_id (readBody F) (key, a) (body F key a) (reads_body F key a h)
  have hlift : Binary.Reads
      (Binary.Reader.lift (checked F (checksum (body F key a)) (body F key a))) (key, a) .empty :=
    Binary.Reads.lift _ (key, a) (by simp [checked, hrun])
  have hb := Binary.Reads.bind (Binary.Reader.bytes (body F key a).size)
    (fun b => Binary.Reader.lift (checked F (checksum (body F key a)) b)) (body F key a) (key, a)
    (body F key a) .empty (Binary.Reads.bytes _) hlift
  rw [ByteArray.append_empty] at hb
  have hn := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.bytes n >>= fun b =>
      Binary.Reader.lift (checked F (checksum (body F key a)) b))
    (body F key a).size (key, a) (Binary.natBE 4 (body F key a).size) (body F key a)
    (Binary.Reads.nat 4 _ h.1) hb
  have hck := Binary.Reads.bind (Binary.Reader.nat 8)
    (fun ck => Binary.Reader.nat 4 >>= fun n => Binary.Reader.bytes n >>= fun b =>
      Binary.Reader.lift (checked F ck b))
    (checksum (body F key a)) (key, a) (Binary.natBE 8 (checksum (body F key a))) _
    (Binary.Reads.nat 8 _ (by
      have := (Flate.fnv64 Flate.fnvOffset (body F key a)).toNat_lt
      simpa [checksum] using this)) hn
  have := Binary.Reads.bind (Binary.Reader.expect F.magic)
    (fun _ => Binary.Reader.nat 8 >>= fun ck => Binary.Reader.nat 4 >>= fun n =>
      Binary.Reader.bytes n >>= fun b => Binary.Reader.lift (checked F ck b))
    () (key, a) F.magic _ (Binary.Reads.expect F.magic) hck
  simpa only [ByteArray.append_assoc] using this

public theorem lookup_exact (key : Array String) (a : α) (h : Bounded F key a) :
    lookup F key (encode F key a) = some a ∧
      ∀ key', key' ≠ key → lookup F key' (encode F key a) = none := by
  have hd := decode_encode_id F key a h
  refine ⟨by simp [lookup, hd], fun key' hne => ?_⟩
  simp only [lookup, hd, Option.bind_some]
  exact ite_eq_right_iff.mpr fun e => absurd (beq_iff_eq.mp e).symm hne

end LeanTex.Core.KeyedRecord
