module

public import LeanTex.Core.KeyedRecord

/-! A cache slot that holds the key it answers: read back as its payload under that key, and as a
miss under any other or when its checksum fails. -/

namespace LeanTex.Core.SlotRecord

open LeanTex.Core

/-- A payload's record: its size, then its bytes. -/
@[expose] public def payloadBytes (payload : ByteArray) : ByteArray :=
  Binary.natBE 4 payload.size ++ payload

public def readPayload : Binary.Reader ByteArray := do
  let size ← Binary.Reader.nat 4
  Binary.Reader.bytes size

private theorem reads_payload (payload : ByteArray) (h : payload.size < 256 ^ 4) :
    Binary.Reads readPayload payload (payloadBytes payload) := by
  have hb := Binary.Reads.bytes payload
  have := Binary.Reads.bind (Binary.Reader.nat 4) Binary.Reader.bytes payload.size payload
    (Binary.natBE 4 payload.size) payload (Binary.Reads.nat 4 _ h) hb
  simpa only [readPayload, payloadBytes] using this

/-- The slot format: its magic, and a payload behind its size. -/
@[expose] public def format : KeyedRecord.Format ByteArray where
  magic := "LTSLOT1\n".toUTF8
  write := payloadBytes
  read := readPayload
  Fits payload := payload.size < 256 ^ 4
  reads := by exact reads_payload
  fits payload := decide (payload.size < 256 ^ 4)
  fits_sound _ := by exact of_decide_eq_true

/-- A payload as a cache stores it under its key. -/
@[expose] public def encode (key : Array String) (payload : ByteArray) : ByteArray :=
  KeyedRecord.encode format key payload

/-- A stored payload read back with its key; `none` for anything else — a
truncated, corrupted or foreign file is a miss. -/
public def decode (bytes : ByteArray) : Option (Array String × ByteArray) :=
  KeyedRecord.decode format bytes

/-- A slot read for a key: its payload where stored under that very key, else a miss. -/
public def lookup (key : Array String) (bytes : ByteArray) : Option ByteArray :=
  KeyedRecord.lookup format key bytes

/-- What a payload needs to fit the format under a key: every length it stores fits 32 bits. -/
@[expose] public def Bounded (key : Array String) (payload : ByteArray) : Prop :=
  KeyedRecord.Bounded format key payload

/-- `Bounded`, decided: what a cache checks before it stores. -/
@[expose] public def storable (key : Array String) (payload : ByteArray) : Bool :=
  KeyedRecord.storable format key payload

public theorem storable_bounded (key : Array String) (payload : ByteArray)
    (h : storable key payload = true) : Bounded key payload :=
  KeyedRecord.storable_bounded format key payload h

public theorem decode_encode_id (key : Array String) (payload : ByteArray)
    (h : Bounded key payload) : decode (encode key payload) = some (key, payload) :=
  KeyedRecord.decode_encode_id format key payload h

public theorem lookup_exact (key : Array String) (payload : ByteArray) (h : Bounded key payload) :
    lookup key (encode key payload) = some payload ∧
      ∀ key', key' ≠ key → lookup key' (encode key payload) = none :=
  KeyedRecord.lookup_exact format key payload h

end LeanTex.Core.SlotRecord
