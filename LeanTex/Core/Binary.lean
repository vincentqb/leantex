import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Lemmas

namespace LeanTex.Core.Binary

/-! Fixed-width binary fields. The laws include arbitrary bytes before and
after a field, so a record codec composes them without depending on its
absolute offsets. Reads are bounds-checked; integer representability is a
mathematical width bound, independent of the decoder. -/

/-- Big-endian bytes, least significant `width` bytes of `n`. -/
def natBE : Nat → Nat → ByteArray
  | 0, _ => .empty
  | width + 1, n => (natBE width (n / 256)).push (UInt8.ofNat n)

/-- Read a fixed-width big-endian natural at a byte offset. -/
def readNatBE : Nat → ByteArray → Nat → Option Nat
  | 0, _, _ => some 0
  | width + 1, bytes, pos => do
      let hi ← readNatBE width bytes pos
      let lo ← bytes[pos + width]?
      return hi * 256 + lo.toNat

@[simp] theorem natBE_size (width n : Nat) : (natBE width n).size = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [natBE, ih]

/-- The byte at the join is the first appended byte. -/
theorem byte_append_exact (pre post : ByteArray) (v : UInt8) :
    (pre ++ [v].toByteArray ++ post)[pre.size]? = some v := by
  rw [getElem?_pos]
  · simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_append,
      List.data_toByteArray, ByteArray.size]
    simp
    exact Array.getElem_push_eq
  · simp only [ByteArray.size_append, List.size_toByteArray, List.length_singleton]
    omega

/-- A fixed-width field is read back in any record context. -/
theorem readNatBE_natBE_id (width n : Nat) (h : n < 256 ^ width)
    (pre post : ByteArray) :
    readNatBE width (pre ++ natBE width n ++ post) pre.size = some n := by
  induction width generalizing n post with
  | zero =>
      have : n = 0 := by simpa using h
      subst n
      rfl
  | succ width ih =>
      have hn : n / 256 < 256 ^ width := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        simpa [Nat.pow_succ] using h
      rw [natBE, ← ByteArray.append_toByteArray_singleton]
      rw [show pre ++ (natBE width (n / 256) ++ [UInt8.ofNat n].toByteArray) ++ post =
        pre ++ natBE width (n / 256) ++ ([UInt8.ofNat n].toByteArray ++ post) by
          simp only [ByteArray.append_assoc]]
      simp only [readNatBE, ih _ hn]
      rw [← ByteArray.append_assoc]
      rw [show pre.size + width = (pre ++ natBE width (n / 256)).size by simp]
      rw [byte_append_exact]
      simp [Nat.mul_comm, Nat.div_add_mod]

/-- A byte reader advances an offset without copying the remaining input. -/
def Reader (α : Type) := ByteArray → Nat → Option (α × Nat)

instance : Monad Reader where
  pure a := fun _ pos => some (a, pos)
  bind read next := fun bytes pos => do
    let (a, pos) ← read bytes pos
    next a bytes pos

/-- Lift a checked tag or other non-consuming decision. -/
def Reader.lift (answer : Option α) : Reader α :=
  fun _ pos => answer.map (·, pos)

def Reader.nat (width : Nat) : Reader Nat :=
  fun bytes pos => (readNatBE width bytes pos).map (·, pos + width)

def Reader.bytes (size : Nat) : Reader ByteArray :=
  fun bytes pos =>
    if pos + size ≤ bytes.size then some (bytes.extract pos (pos + size), pos + size)
    else none

/-- Interpret a field, refusing unknown tags without consuming another field. -/
def Reader.map? (read : Reader α) (f : α → Option β) : Reader β :=
  fun bytes pos => do
    let (a, pos) ← read bytes pos
    let b ← f a
    return (b, pos)

def Reader.expect (expected : ByteArray) : Reader Unit :=
  (Reader.bytes expected.size).map? fun actual =>
    if actual == expected then some () else none

/-- A parser consumes precisely this field in every enclosing record. -/
def Reads (read : Reader α) (value : α) (encoded : ByteArray) : Prop :=
  ∀ pre post, read (pre ++ encoded ++ post) pre.size =
    some (value, pre.size + encoded.size)

theorem Reads.pure (value : α) : Reads (pure value) value .empty := by
  intro pre post
  change some (value, pre.size) = some (value, pre.size + ByteArray.empty.size)
  rfl

theorem Reads.lift (answer : Option α) (value : α) (h : answer = some value) :
    Reads (Reader.lift answer) value .empty := by
  subst h
  intro pre post
  simp [Reader.lift]

theorem Reads.bind (read : Reader α) (next : α → Reader β)
    (a : α) (b : β) (ea eb : ByteArray)
    (ha : Reads read a ea) (hb : Reads (next a) b eb) :
    Reads (read >>= next) b (ea ++ eb) := by
  intro pre post
  change (do
    let (a, pos) ← read (pre ++ (ea ++ eb) ++ post) pre.size
    next a (pre ++ (ea ++ eb) ++ post) pos) = _
  rw [show pre ++ (ea ++ eb) ++ post = pre ++ ea ++ (eb ++ post) by
    simp only [ByteArray.append_assoc], ha]
  change next a (pre ++ ea ++ (eb ++ post)) (pre.size + ea.size) = _
  rw [show pre.size + ea.size = (pre ++ ea).size by simp]
  rw [← ByteArray.append_assoc, hb]
  simp [Nat.add_assoc]

theorem Reads.nat (width n : Nat) (h : n < 256 ^ width) :
    Reads (Reader.nat width) n (natBE width n) := by
  intro pre post
  simp [Reader.nat, readNatBE_natBE_id width n h]

theorem Reads.bytes (value : ByteArray) :
    Reads (Reader.bytes value.size) value value := by
  intro pre post
  have h : pre.size + value.size ≤ (pre ++ value ++ post).size := by simp
  simp only [Reader.bytes, h, ↓reduceIte]
  rw [ByteArray.append_assoc]
  have hex := ByteArray.extract_append_size_add (i := 0) (j := value.size)
    (a := pre) (b := value ++ post)
  simp only [Nat.add_zero] at hex
  rw [hex, ByteArray.extract_append_eq_left rfl]

theorem Reads.map? (read : Reader α) (f : α → Option β) (a : α) (b : β)
    (encoded : ByteArray) (h : Reads read a encoded) (hf : f a = some b) :
    Reads (read.map? f) b encoded := by
  intro pre post
  simp [Reader.map?, h pre post, hf]

theorem Reads.expect (expected : ByteArray) :
    Reads (Reader.expect expected) () expected :=
  Reads.map? _ _ _ _ _ (Reads.bytes expected) (by
    change (if expected.data == expected.data then some () else none) = some ()
    simp)

/-- Encode an array with one accumulating byte buffer. -/
def array (encode : α → ByteArray) (values : Array α) : ByteArray :=
  values.foldl (fun out value => out ++ encode value) .empty

private theorem array_acc (encode : α → ByteArray) (values : List α) (pre : ByteArray) :
    values.foldl (fun out value => out ++ encode value) pre =
      pre ++ array encode values.toArray := by
  simp only [array, List.foldl_toArray]
  induction values generalizing pre with
  | nil => simp
  | cons value values ih =>
      simp only [List.foldl_cons, ByteArray.empty_append]
      rw [ih (pre ++ encode value), ih (encode value)]
      simp only [ByteArray.append_assoc]

@[simp] theorem array_nil (encode : α → ByteArray) : array encode #[] = .empty := rfl

theorem array_cons (encode : α → ByteArray) (value : α) (values : List α) :
    array encode (value :: values).toArray =
      encode value ++ array encode values.toArray := by
  simp only [array, List.foldl_toArray, List.foldl_cons, ByteArray.empty_append]
  simpa only [array, List.foldl_toArray] using array_acc encode values (encode value)

theorem array_size (encode : α → ByteArray) (values : Array α) (width : Nat)
    (h : ∀ v ∈ values, (encode v).size = width) :
    (array encode values).size = width * values.size := by
  rcases values with ⟨values⟩
  induction values with
  | nil => simp [array]
  | cons value values ih =>
      rw [show (⟨value :: values⟩ : Array α) = (value :: values).toArray from rfl,
        array_cons]
      simp only [ByteArray.size_append]
      rw [h value (by simp), ih (fun v hv => h v (by simp_all))]
      simp [Nat.mul_add, Nat.add_comm]

private def Reader.arrayLoop (read : Reader α) : Nat → Array α → Reader (Array α)
  | 0, acc => pure acc
  | count + 1, acc => do
      let value ← read
      arrayLoop read count (acc.push value)

/-- Read fixed-width elements. Check the declared extent before allocating
or entering the loop. For a positive element width, the file bounds the count. -/
def Reader.array (width count : Nat) (read : Reader α) : Reader (Array α) :=
  fun bytes pos =>
    if pos + width * count ≤ bytes.size then Reader.arrayLoop read count #[] bytes pos
    else none

private theorem Reads.arrayLoop (read : Reader α) (encode : α → ByteArray)
    (values : List α) (acc : Array α) (h : ∀ v ∈ values, Reads read v (encode v)) :
    Reads (Reader.arrayLoop read values.length acc) (acc ++ values.toArray)
      (array encode values.toArray) := by
  induction values generalizing acc with
  | nil => simpa [Reader.arrayLoop] using Reads.pure acc
  | cons value values ih =>
      rw [array_cons]
      have heq : acc ++ (value :: values).toArray = acc.push value ++ values.toArray := by
        apply Array.ext'
        simp
      rw [heq]
      exact Reads.bind read (fun v => Reader.arrayLoop read values.length (acc.push v))
          value (acc.push value ++ values.toArray) (encode value)
          (array encode values.toArray)
          (h value (by simp)) (ih _ (fun v hv => h v (by simp [hv])))

theorem Reads.array (read : Reader α) (encode : α → ByteArray) (values : Array α)
    (width : Nat) (hs : ∀ v ∈ values, (encode v).size = width)
    (h : ∀ v ∈ values, Reads read v (encode v)) :
    Reads (Reader.array width values.size read) values (Binary.array encode values) := by
  intro pre post
  have hsize : pre.size + width * values.size ≤
      (pre ++ Binary.array encode values ++ post).size := by
    simp [array_size encode values width hs]
  simp only [Reader.array, hsize, ↓reduceIte]
  simpa using Reads.arrayLoop read encode values.toList #[] (by simpa using h) pre post

/-- Reject trailing bytes after the record parser succeeds. -/
def Reader.run (read : Reader α) (bytes : ByteArray) : Option α := do
  let (value, pos) ← read bytes 0
  if pos == bytes.size then some value else none

theorem Reads.run_id (read : Reader α) (value : α) (encoded : ByteArray)
    (h : Reads read value encoded) : read.run encoded = some value := by
  have hr := h .empty .empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_add] at hr
  simp [Reader.run, hr]

end LeanTex.Core.Binary
