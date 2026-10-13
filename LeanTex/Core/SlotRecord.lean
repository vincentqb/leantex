module

public import LeanTex.Core.Binary
public import LeanTex.Core.Flate

/-! A cache slot that holds the key it answers: read back as its payload under that key, and as a
miss under any other or when its checksum fails. -/

namespace LeanTex.Core.SlotRecord

open LeanTex.Core

/-- A slot's body: the key its payload answers — its parts' count, then
each — and the payload, its size first. -/
@[expose] public def body (key : Array String) (payload : ByteArray) : ByteArray :=
  Binary.natBE 4 key.size ++ Binary.array Binary.str key ++ Binary.natBE 4 payload.size ++ payload

public def readBody : Binary.Reader (Array String × ByteArray) := do
  let n ← Binary.Reader.nat 4
  let key ← Binary.Reader.many Binary.Reader.str n #[]
  let size ← Binary.Reader.nat 4
  let payload ← Binary.Reader.bytes size
  return (key, payload)

/-- The file's first bytes. -/
@[expose] public def magic : ByteArray := "LTSLOT1\n".toUTF8

/-- A body's checksum (FNV-64, `Flate.fnv64`). -/
@[expose] public def checksum (b : ByteArray) : Nat := (Flate.fnv64 14695981039346656037 b).toNat

/-- A payload as a cache stores it under its key: magic, checksum, size, body. -/
@[expose] public def encode (key : Array String) (payload : ByteArray) : ByteArray :=
  let b := body key payload
  magic ++ Binary.natBE 8 (checksum b) ++ Binary.natBE 4 b.size ++ b

/-- The last step of reading a file: the body, where its checksum holds. -/
public def checked (ck : Nat) (b : ByteArray) : Option (Array String × ByteArray) :=
  if checksum b == ck then readBody.run b else none

public def readAll : Binary.Reader (Array String × ByteArray) := do
  Binary.Reader.expect magic
  let ck ← Binary.Reader.nat 8
  let n ← Binary.Reader.nat 4
  let b ← Binary.Reader.bytes n
  Binary.Reader.lift (checked ck b)

/-- A stored payload read back with its key; `none` for anything else — a
truncated, corrupted or foreign file is a miss. -/
public def decode (bytes : ByteArray) : Option (Array String × ByteArray) := readAll.run bytes

/-- A slot read for a key: its payload where stored under that very key, else a miss. -/
public def lookup (key : Array String) (bytes : ByteArray) : Option ByteArray :=
  (decode bytes).bind fun (k, p) => if k == key then some p else none

/-- What a payload needs to fit the format under a key: every length it
stores fits 32 bits. -/
@[expose] public def Bounded (key : Array String) (payload : ByteArray) : Prop :=
  (body key payload).size < 256 ^ 4 ∧ key.size < 256 ^ 4 ∧
    (∀ s ∈ key, s.toUTF8.size < 256 ^ 4) ∧ payload.size < 256 ^ 4

/-- `Bounded`, decided: what a cache checks before it stores. -/
public def storable (key : Array String) (payload : ByteArray) : Bool :=
  decide ((body key payload).size < 256 ^ 4) && decide (key.size < 256 ^ 4) &&
    key.all (fun s => decide (s.toUTF8.size < 256 ^ 4)) && decide (payload.size < 256 ^ 4)

public theorem storable_bounded (key : Array String) (payload : ByteArray)
    (h : storable key payload = true) : Bounded key payload := by
  simp only [storable, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨hb, hk⟩, hs⟩, hp⟩ := h
  refine ⟨hb, hk, fun s hm => ?_, hp⟩
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hm
  simpa using hs i hi

private theorem reads_body (key : Array String) (payload : ByteArray) (h : Bounded key payload) :
    Binary.Reads readBody (key, payload) (body key payload) := by
  obtain ⟨_, hk, hks, hp⟩ := h
  unfold readBody body
  have hpay := Binary.Reads.bind (Binary.Reader.bytes payload.size)
    (fun payload => (pure (key, payload) : Binary.Reader (Array String × ByteArray)))
    payload (key, payload) payload .empty (Binary.Reads.bytes payload) (Binary.Reads.pure _)
  rw [ByteArray.append_empty] at hpay
  have hsize := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun size => Binary.Reader.bytes size >>= fun payload =>
      (pure (key, payload) : Binary.Reader (Array String × ByteArray)))
    payload.size (key, payload) (Binary.natBE 4 payload.size) payload
    (Binary.Reads.nat 4 _ hp) hpay
  have hmany := Binary.Reads.many Binary.Reader.str Binary.str key.toList #[]
    (fun s hm => Binary.Reads.str s (hks s (by simpa using hm)))
  simp only [Array.empty_append, Array.toArray_toList, Array.length_toList] at hmany
  have hkey := Binary.Reads.bind (Binary.Reader.many Binary.Reader.str key.size #[])
    (fun key => Binary.Reader.nat 4 >>= fun size => Binary.Reader.bytes size >>= fun payload =>
      (pure (key, payload) : Binary.Reader (Array String × ByteArray)))
    key (key, payload) (Binary.array Binary.str key) (Binary.natBE 4 payload.size ++ payload)
    hmany hsize
  have := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.many Binary.Reader.str n #[] >>= fun key =>
      Binary.Reader.nat 4 >>= fun size => Binary.Reader.bytes size >>= fun payload =>
        (pure (key, payload) : Binary.Reader (Array String × ByteArray)))
    key.size (key, payload) (Binary.natBE 4 key.size) _ (Binary.Reads.nat 4 _ hk) hkey
  simpa only [ByteArray.append_assoc] using this

public theorem decode_encode_id (key : Array String) (payload : ByteArray)
    (h : Bounded key payload) : decode (encode key payload) = some (key, payload) := by
  unfold decode
  apply Binary.Reads.run_id
  unfold readAll encode
  have hrun : readBody.run (body key payload) = some (key, payload) :=
    Binary.Reads.run_id readBody (key, payload) (body key payload) (reads_body key payload h)
  have hlift : Binary.Reads (Binary.Reader.lift (checked (checksum (body key payload)) (body key payload)))
      (key, payload) .empty :=
    Binary.Reads.lift _ (key, payload) (by simp [checked, hrun])
  have hb := Binary.Reads.bind (Binary.Reader.bytes (body key payload).size)
    (fun b => Binary.Reader.lift (checked (checksum (body key payload)) b)) (body key payload)
    (key, payload) (body key payload) .empty (Binary.Reads.bytes _) hlift
  rw [ByteArray.append_empty] at hb
  have hn := Binary.Reads.bind (Binary.Reader.nat 4)
    (fun n => Binary.Reader.bytes n >>= fun b =>
      Binary.Reader.lift (checked (checksum (body key payload)) b))
    (body key payload).size (key, payload) (Binary.natBE 4 (body key payload).size)
    (body key payload) (Binary.Reads.nat 4 _ h.1) hb
  have hck := Binary.Reads.bind (Binary.Reader.nat 8)
    (fun ck => Binary.Reader.nat 4 >>= fun n => Binary.Reader.bytes n >>= fun b =>
      Binary.Reader.lift (checked ck b))
    (checksum (body key payload)) (key, payload) (Binary.natBE 8 (checksum (body key payload))) _
    (Binary.Reads.nat 8 _ (by
      have := (Flate.fnv64 14695981039346656037 (body key payload)).toNat_lt
      simpa [checksum] using this)) hn
  have := Binary.Reads.bind (Binary.Reader.expect magic)
    (fun _ => Binary.Reader.nat 8 >>= fun ck => Binary.Reader.nat 4 >>= fun n =>
      Binary.Reader.bytes n >>= fun b => Binary.Reader.lift (checked ck b))
    () (key, payload) magic _ (Binary.Reads.expect magic) hck
  simpa only [ByteArray.append_assoc] using this

public theorem lookup_exact (key : Array String) (payload : ByteArray) (h : Bounded key payload) :
    lookup key (encode key payload) = some payload ∧
      ∀ key', key' ≠ key → lookup key' (encode key payload) = none := by
  have hd := decode_encode_id key payload h
  refine ⟨by simp [lookup, hd], fun key' hne => ?_⟩
  simp only [lookup, hd, Option.bind_some]
  exact ite_eq_right_iff.mpr fun e => absurd (beq_iff_eq.mp e).symm hne

end LeanTex.Core.SlotRecord
