module

public import LeanTex.Core.Binary

namespace LeanTex.Core.Pdf.Xref

/-! The writer's cross-reference fields, ISO 32000-2 §7.5.8.3. The type
field is one byte; the other two take the widths their largest values
need (`widthsOf`), as pdfTeX and LuaTeX size `/W`, so no offset, object
number or stream index meets a ceiling the writer chose. These laws are
artifact-specific byte bookkeeping. -/

/-- The byte widths of the second and third fields: `/W [1 first second]`. -/
public structure Widths where
  first : Nat
  second : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Bytes per row, the type byte included. -/
@[expose] public def Widths.row (w : Widths) : Nat := 1 + w.first + w.second

/-- One cross-reference row: type, byte offset or object-stream number,
generation or index within the object stream. -/
public def row (w : Widths) (kind : UInt8) (first second : Nat) : ByteArray :=
  let kindBytes := Binary.natBE 1 kind.toNat
  let firstBytes := Binary.natBE w.first first
  let secondBytes := Binary.natBE w.second second
  kindBytes ++ firstBytes ++ secondBytes

@[simp] public theorem row_size_exact (w : Widths) (kind : UInt8) (first second : Nat) :
    (row w kind first second).size = w.row := by
  simp [row, Widths.row]

/-- Every field reads back at its declared offset, inside any surrounding
file, provided the two integer fields are representable in their widths. -/
public theorem row_fields_exact (w : Widths) (kind : UInt8) (first second : Nat)
    (hfirst : first < 256 ^ w.first) (hsecond : second < 256 ^ w.second)
    (pre post : ByteArray) :
    Binary.readNatBE 1 (pre ++ row w kind first second ++ post) pre.size =
      some kind.toNat ∧
    Binary.readNatBE w.first (pre ++ row w kind first second ++ post) (pre.size + 1) =
      some first ∧
    Binary.readNatBE w.second (pre ++ row w kind first second ++ post)
      (pre.size + 1 + w.first) = some second := by
  constructor
  · simpa only [row, ByteArray.append_assoc] using
      Binary.readNatBE_natBE_id 1 kind.toNat kind.toNat_lt_size pre
        (Binary.natBE w.first first ++ Binary.natBE w.second second ++ post)
  constructor
  · simpa only [row, ByteArray.append_assoc, ByteArray.size_append,
      Binary.natBE_size] using
      Binary.readNatBE_natBE_id w.first first hfirst
        (pre ++ Binary.natBE 1 kind.toNat) (Binary.natBE w.second second ++ post)
  · simpa only [row, ByteArray.append_assoc, ByteArray.size_append,
      Binary.natBE_size, Nat.add_assoc] using
      Binary.readNatBE_natBE_id w.second second hsecond
        (pre ++ Binary.natBE 1 kind.toNat ++ Binary.natBE w.first first) post

/-- The three row types of §7.5.8.3. The second field of a compressed
entry is an index, not an object number or a byte offset. -/
public inductive Entry where
  | free (next generation : Nat)
  | direct (offset generation : Nat)
  | compressed (stream index : Nat)
  deriving Repr, BEq

@[expose] public def Entry.fields : Entry → UInt8 × Nat × Nat
  | .free next gen => (0, next, gen)
  | .direct off gen => (1, off, gen)
  | .compressed stm idx => (2, stm, idx)

/-- Precisely the two representability requirements of `/W [1 first second]`.
This is a numeric input domain, independent of encoding or decoding. -/
@[expose] public def Entry.Fits (w : Widths) (e : Entry) : Prop :=
  e.fields.2.1 < 256 ^ w.first ∧ e.fields.2.2 < 256 ^ w.second

public def Entry.bytes (w : Widths) (e : Entry) : ByteArray :=
  row w e.fields.1 e.fields.2.1 e.fields.2.2

@[simp] public theorem Entry.bytes_size (w : Widths) (e : Entry) : (e.bytes w).size = w.row :=
  row_size_exact _ _ _ _

/-- The actual writer's accumulator for its cross-reference payload. -/
def encodeList (w : Widths) (out : ByteArray) : List Entry → ByteArray
  | [] => out
  | e :: es => encodeList w (out ++ e.bytes w) es

public def encode (w : Widths) (es : Array Entry) : ByteArray :=
  encodeList w ByteArray.empty es.toList

theorem encodeList_bytes (w : Widths) (out : ByteArray) (es : List Entry) :
    encodeList w out es = out ++ encodeList w ByteArray.empty es := by
  induction es generalizing out with
  | nil => simp [encodeList]
  | cons e es ih =>
    simp only [encodeList]
    rw [ih (out ++ e.bytes w), ih (ByteArray.empty ++ e.bytes w)]
    simp [ByteArray.append_assoc]

theorem encodeList_append (w : Widths) (out : ByteArray) (xs ys : List Entry) :
    encodeList w out (xs ++ ys) = encodeList w (encodeList w out xs) ys := by
  induction xs generalizing out with
  | nil => rfl
  | cons e es ih => exact ih _

theorem encodeList_size (w : Widths) (out : ByteArray) (es : List Entry) :
    (encodeList w out es).size = out.size + w.row * es.length := by
  induction es generalizing out with
  | nil => simp [encodeList]
  | cons e es ih =>
    simp only [encodeList, ih, ByteArray.size_append, Entry.bytes_size, List.length_cons,
      Nat.mul_succ]
    omega

@[simp] public theorem encode_size_exact (w : Widths) (es : Array Entry) :
    (encode w es).size = w.row * es.size := by
  simp [encode, encodeList_size]

/-- All three fields of any row in the writer's payload, at the byte
position determined by its index. Prefix and suffix bytes are arbitrary.
Only this row needs to fit; nothing is assumed about the encoder. -/
public theorem encode_entry_fields_exact (w : Widths) (before after : Array Entry) (e : Entry)
    (he : e.Fits w) (pre post : ByteArray) :
    let data := pre ++ encode w (before ++ #[e] ++ after) ++ post
    let pos := pre.size + w.row * before.size
    Binary.readNatBE 1 data pos = some e.fields.1.toNat ∧
    Binary.readNatBE w.first data (pos + 1) = some e.fields.2.1 ∧
    Binary.readNatBE w.second data (pos + 1 + w.first) = some e.fields.2.2 := by
  have hbytes :
      encode w (before ++ #[e] ++ after) = encode w before ++ e.bytes w ++ encode w after := by
    simp only [encode, Array.toList_append,
      encodeList_append, encodeList]
    rw [encodeList_bytes]
  simpa only [hbytes, ByteArray.append_assoc, Entry.bytes, ByteArray.size_append,
    encode_size_exact, Nat.add_assoc] using
    row_fields_exact w e.fields.1 e.fields.2.1 e.fields.2.2 he.1 he.2
      (pre ++ encode w before) (encode w after ++ post)

/-- Any selected encoded row, at the position declared by its array index.
The surrounding bytes are arbitrary; only the selected row must fit. -/
public theorem encode_index_fields_exact (w : Widths) (es : Array Entry) (i : Nat) (e : Entry)
    (hi : es[i]? = some e) (he : e.Fits w) (pre post : ByteArray) :
    let data := pre ++ encode w es ++ post
    let pos := pre.size + w.row * i
    Binary.readNatBE 1 data pos = some e.fields.1.toNat ∧
    Binary.readNatBE w.first data (pos + 1) = some e.fields.2.1 ∧
    Binary.readNatBE w.second data (pos + 1 + w.first) = some e.fields.2.2 := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hi
  have hsplit : es.extract 0 i ++ #[e] ++ es.extract (i + 1) es.size = es := by
    rw [← heq, ← Array.push_eq_append, Array.push_extract_getElem hlt]
    simp [Nat.max_eq_right (by omega : i + 1 ≤ es.size)]
  have h := encode_entry_fields_exact w (es.extract 0 i) (es.extract (i + 1) es.size)
    e he pre post
  simpa only [hsplit, Array.size_extract, Nat.min_eq_left (by omega : i ≤ es.size),
    Nat.sub_zero] using h

/-- The fewest bytes, never zero, a field needs to hold `n`: a zero width
would declare the field absent (ISO 32000-2 §7.5.8.2). -/
public def width (n : Nat) : Nat :=
  if n < 256 then 1 else width (n / 256) + 1
termination_by n
decreasing_by omega

/-- **`width_between`**: `n` needs every byte `width` gives it and fits
in them — the width is the least one, at least one byte, that holds `n`. -/
public theorem width_between (n : Nat) :
    1 ≤ width n ∧ (width n = 1 ∨ 256 ^ (width n - 1) ≤ n) ∧ n < 256 ^ width n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [width]
    split
    · rename_i h
      exact ⟨Nat.le_refl 1, Or.inl rfl, by simpa using h⟩
    · rename_i h
      obtain ⟨_, hlo, hhi⟩ := ih (n / 256) (by omega)
      refine ⟨by omega, Or.inr ?_, ?_⟩
      · rw [Nat.add_sub_cancel]
        rcases hlo with hw | hw
        · rw [hw]
          omega
        · have hk : width (n / 256) = width (n / 256) - 1 + 1 := by
            have := (ih (n / 256) (by omega)).1
            omega
          rw [hk, Nat.pow_succ]
          have := Nat.mul_le_mul_right 256 hw
          omega
      · rw [Nat.pow_succ]
        have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mp hhi
        omega

/-- `width_between`'s lower bound read the other way: a field of at least
one byte that holds `n` is at least `width n` wide. -/
private theorem width_le_of_lt (n k : Nat) (hk : 1 ≤ k) (h : n < 256 ^ k) : width n ≤ k := by
  obtain ⟨_, hlo, _⟩ := width_between n
  rcases hlo with hw | hw
  · omega
  · have hlt : 256 ^ (width n - 1) < 256 ^ k := Nat.lt_of_le_of_lt hw h
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 256)).mp hlt
    omega

private theorem foldl_max_ge {α : Type} (f : α → Nat) (xs : List α) (acc : Nat) :
    acc ≤ xs.foldl (fun m e => max m (f e)) acc ∧
      ∀ x ∈ xs, f x ≤ xs.foldl (fun m e => max m (f e)) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := ih (max acc (f x))
    refine ⟨by simp only [List.foldl_cons]; omega, ?_⟩
    intro y hy
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · exact h2 y hy

private theorem foldl_max_lt {α : Type} (f : α → Nat) (xs : List α) (acc b : Nat)
    (ha : acc < b) (hx : ∀ x ∈ xs, f x < b) :
    xs.foldl (fun m e => max m (f e)) acc < b := by
  induction xs generalizing acc with
  | nil => simpa using ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by have := hx x List.mem_cons_self; omega)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

/-- The largest second and third field among the rows. -/
@[expose] public def maxFirst (es : Array Entry) : Nat :=
  es.foldl (fun m e => max m e.fields.2.1) 0

@[expose] public def maxSecond (es : Array Entry) : Nat :=
  es.foldl (fun m e => max m e.fields.2.2) 0

/-- The `/W` the writer declares: each field as wide as its largest value needs. -/
@[expose] public def widthsOf (es : Array Entry) : Widths :=
  ⟨width (maxFirst es), width (maxSecond es)⟩

/-- Every row fits the widths computed from the rows: the field bounds the
old fixed `/W [1 4 2]` needed as premises hold by construction. -/
public theorem widthsOf_fits (es : Array Entry) : ∀ e ∈ es, e.Fits (widthsOf es) := by
  intro e he
  have hm := Array.mem_toList_iff.mpr he
  simp only [Entry.Fits, widthsOf, maxFirst, maxSecond, ← Array.foldl_toList]
  exact ⟨Nat.lt_of_le_of_lt ((foldl_max_ge (fun e : Entry => e.fields.2.1) es.toList 0).2 e hm)
      (width_between _).2.2,
    Nat.lt_of_le_of_lt ((foldl_max_ge (fun e : Entry => e.fields.2.2) es.toList 0).2 e hm)
      (width_between _).2.2⟩

/-- **`widthsOf_between`**: each computed width lies between one byte and
the width of any `/W` of nonzero widths that every row fits — the computed
widths are the narrowest a fitting `/W` could declare. -/
public theorem widthsOf_between (es : Array Entry) (w : Widths) (h1 : 1 ≤ w.first)
    (h2 : 1 ≤ w.second) (hw : ∀ e ∈ es, e.Fits w) :
    (1 ≤ (widthsOf es).first ∧ (widthsOf es).first ≤ w.first) ∧
      (1 ≤ (widthsOf es).second ∧ (widthsOf es).second ≤ w.second) := by
  have hpos (k : Nat) : 0 < 256 ^ k := Nat.pow_pos (by decide)
  simp only [widthsOf, maxFirst, maxSecond, ← Array.foldl_toList]
  refine ⟨⟨(width_between _).1, width_le_of_lt _ _ h1 ?_⟩,
    ⟨(width_between _).1, width_le_of_lt _ _ h2 ?_⟩⟩
  · exact foldl_max_lt (fun e : Entry => e.fields.2.1) es.toList 0 _ (hpos _)
      (fun e he => (hw e (Array.mem_toList_iff.mp he)).1)
  · exact foldl_max_lt (fun e : Entry => e.fields.2.2) es.toList 0 _ (hpos _)
      (fun e he => (hw e (Array.mem_toList_iff.mp he)).2)

end LeanTex.Core.Pdf.Xref
