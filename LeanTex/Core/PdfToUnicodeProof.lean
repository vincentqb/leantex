module

public import LeanTex.Core.PdfToUnicode
public import LeanTex.Core.PdfFont
public import LeanTex.Core.PdfContentLexProof
public import LeanTex.Core.PdfTextProof
import all LeanTex.Core.PdfToUnicode
import all LeanTex.Core.PdfFont
import all LeanTex.Core.PdfContentLex
import all LeanTex.Core.PdfContentLexProof
import Std.Data.HashMap.Lemmas

/-! The ToUnicode CMap the writer embeds reads back, through the reader's CMap parser, as one
character per code: each used glyph's code to the first character `painted` lists it with. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Layout LeanTex.Core.Font
open LeanTex.Core.PdfContentLex (Tok TokSpelled Spelled OpSpelled ValSpelled leadR)
open LeanTex.Core.PdfRead (Obj)

/-! ### The CMap's tokens are spelled -/

theorem spelled_of_all : ∀ (ts : List Tok), (∀ t ∈ ts, TokSpelled t) → (∀ t ∈ ts, leadR t = false) →
    Spelled ts
  | [], _, _ => trivial
  | t :: rest, hs, hr =>
    ⟨hs t (by simp), fun _ _ _ u hu => by
      cases rest with
      | nil => simp at hu
      | cons v rest => simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hu; subst hu; exact hr v (by simp),
     spelled_of_all rest (fun u hu => hs u (by simp [hu])) (fun u hu => hr u (by simp [hu]))⟩

theorem hexObj_spelled (ds : String) (h : ∀ c ∈ ds.toList, c.toNat < 256 ∧ Hex.val? c.toNat ≠ none) :
    ValSpelled (hexObj ds) := by
  refine ⟨PdfRead.strOf_representable _ ?_ (Obj.StringSpelling.hex ?_), fun n g => by simp [hexObj, PdfRead.strOf]⟩
  · intro b hb
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hb
    rcases hb with (rfl | ⟨x, hx, rfl⟩) | rfl
    · decide
    · exact (h x hx).1
    · decide
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact Or.inl (h x hx).2

theorem digits_hex (w n : Nat) : ∀ c ∈ (Hex.digits true w n).toList, c.toNat < 256 ∧ Hex.val? c.toNat ≠ none := by
  intro c hc
  simp only [Hex.digits, String.toList_ofList] at hc
  exact PdfRead.hexDigit_spelled c (Hex.digitList_mem hc)

theorem utf16Hex_hex (ch : Char) : ∀ c ∈ (PdfRead.utf16Hex ch).toList, c.toNat < 256 ∧ Hex.val? c.toNat ≠ none :=
  fun c hc => PdfRead.hexDigit_spelled c (PdfRead.utf16Hex_spelled ch c hc)

theorem name_spelled (s : String) (h : Obj.NameSpelling s) : ValSpelled (.name s) :=
  ⟨.name h, fun _ _ => by simp⟩

theorem int_spelled (n : Int) : ValSpelled (.int n) := ⟨.int n, fun _ _ => by simp⟩

theorem op_spelled (n : String) (ne : n.toList ≠ []) (ascii : ∀ c ∈ n.toList, c.toNat < 128)
    (reg : ∀ c ∈ n.toList, PdfContentLex.regular c.toNat = true)
    (lead : ∀ c, n.toList.head? = some c → PdfLex.numByte c.toNat = false)
    (word : n ≠ "true" ∧ n ≠ "false" ∧ n ≠ "null" ∧ n ≠ "BI" ∧ n ≠ "R") : TokSpelled (.op n) :=
  ⟨ne, ascii, reg, lead, word⟩

theorem sysInfo_spelled : ValSpelled (.dict #[("Registry", PdfRead.literal "Adobe".toUTF8),
    ("Ordering", PdfRead.literal "UCS".toUTF8), ("Supplement", .int 0)]) := by
  refine ⟨.dict ?_ ?_, fun _ _ => by simp⟩
  · intro e he
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> (unfold Obj.NameSpelling; decide)
  · intro e he
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact PdfRead.literal_representable _
    · exact PdfRead.literal_representable _
    · exact .int 0

theorem cmapHead_spelled : ∀ t ∈ cmapHead, TokSpelled t.1 ∧ leadR t.1 = false := by
  intro t ht
  simp only [cmapHead, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, rfl⟩
  all_goals dsimp only
  all_goals first
    | exact name_spelled _ (by unfold Obj.NameSpelling; decide)
    | exact int_spelled _
    | exact sysInfo_spelled
    | exact hexObj_spelled _ (by decide)
    | (apply op_spelled <;> decide)

theorem cmapTail_spelled : ∀ t ∈ cmapTail, TokSpelled t.1 ∧ leadR t.1 = false := by
  intro t ht
  simp only [cmapTail, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, rfl⟩
  all_goals dsimp only
  all_goals first
    | exact name_spelled _ (by unfold Obj.NameSpelling; decide)
    | (apply op_spelled <;> decide)

theorem bfcharSection_spelled (chunk : List (Nat × Char)) :
    ∀ t ∈ bfcharSection chunk, TokSpelled t.1 ∧ leadR t.1 = false := by
  intro t ht
  simp only [bfcharSection, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at ht
  rcases ht with ((rfl | rfl) | ⟨p, -, hp⟩) | rfl
  · exact ⟨int_spelled _, rfl⟩
  · exact ⟨op_spelled _ (by decide) (by decide) (by decide) (by decide) (by decide), rfl⟩
  · simp only [bfcharPair, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨hexObj_spelled _ (digits_hex 4 p.1), rfl⟩
    · exact ⟨hexObj_spelled _ (utf16Hex_hex p.2), rfl⟩
  · exact ⟨op_spelled _ (by decide) (by decide) (by decide) (by decide) (by decide), rfl⟩

theorem cmapToks_spelled (used : List (Nat × Char)) :
    ∀ t ∈ cmapToks used, TokSpelled t.1 ∧ leadR t.1 = false := by
  intro t ht
  simp only [cmapToks, List.mem_append, List.mem_flatMap] at ht
  rcases ht with (ht | ⟨c, -, hc⟩) | ht
  · exact cmapHead_spelled t ht
  · exact bfcharSection_spelled c t hc
  · exact cmapTail_spelled t ht

theorem cmapToks_ws (used : List (Nat × Char)) :
    ∀ t ∈ cmapToks used, PdfLex.isWs t.2.toNat = true := by
  intro t ht
  simp only [cmapToks, List.mem_append, List.mem_flatMap] at ht
  rcases ht with (ht | ⟨c, -, hc⟩) | ht
  · simp only [cmapHead, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (subst h; rfl)
  · simp only [bfcharSection, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap] at hc
    rcases hc with ((h | h) | ⟨p, -, hp⟩) | h
    · subst h; rfl
    · subst h; rfl
    · simp only [bfcharPair, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h <;> (subst h; rfl)
    · subst h; rfl
  · simp only [cmapTail, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h | h | h | h | h <;> (subst h; rfl)

/-- The CMap's bytes scan back as its tokens. -/
theorem scan_toUnicodeCMap (used : Array (Nat × Char)) :
    PdfContentLex.scan (toUnicodeCMap used) = ((cmapToks used.toList).map (·.1)).toArray := by
  unfold toUnicodeCMap
  have hs := cmapToks_spelled used.toList
  exact PdfContentLex.scan_renderSep_exact false _
    (spelled_of_all _ (fun t ht => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht; exact (hs u hu).1)
      (fun t ht => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht; exact (hs u hu).2))
    (cmapToks_ws used.toList)

/-! ### Codes and characters decode -/

/-- A hexadecimal digit's byte. -/
@[expose] public def digitByte (c : Char) : UInt8 := Nat.toUInt8 c.toNat

public theorem digitByte_eq (c : Char) : digitByte c = UInt8.ofNat c.toNat := rfl

public theorem digitByte_spell (k : Nat) : (digitByte (Hex.spell true k)).toNat = (Hex.spell true k).toNat := by
  have := Hex.spell_ascii true k
  simp only [digitByte, Nat.toUInt8, UInt8.toNat_ofNat']
  omega

public theorem hexStep_spell_none (acc : ByteArray) (k : Nat) :
    PdfContentLex.hexStep (acc, none) (digitByte (Hex.spell true k)) = (acc, some (k % 16)) := by
  simp [PdfContentLex.hexStep, digitByte_spell, Hex.val?_spell_exact]

public theorem hexStep_spell_some (acc : ByteArray) (h k : Nat) :
    PdfContentLex.hexStep (acc, some h) (digitByte (Hex.spell true k)) =
      (acc.push (UInt8.ofNat (h * 16 + k % 16)), none) := by
  simp [PdfContentLex.hexStep, digitByte_spell, Hex.val?_spell_exact]

public theorem digitList4 (n : Nat) : Hex.digitList true 4 n =
    [Hex.spell true (n / 16 / 16 / 16), Hex.spell true (n / 16 / 16), Hex.spell true (n / 16),
      Hex.spell true n] := by
  simp [Hex.digitList]

/-- Four hexadecimal digits read as their two bytes. -/
public theorem hexStep_digits4 (acc : ByteArray) (n : Nat) :
    ((Hex.digits true 4 n).toList.map digitByte).foldl PdfContentLex.hexStep (acc, none) =
      ((acc.push (UInt8.ofNat (n / 256 % 256))).push (UInt8.ofNat (n % 256)), none) := by
  simp only [Hex.digits, String.toList_ofList, digitList4, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil, hexStep_spell_none, hexStep_spell_some]
  congr 3 <;> first | omega | (apply UInt8.toNat_inj.mp; simp only [UInt8.toNat_ofNat']; omega)

/-- A hex string's bytes from its delimited spelling of digits. -/
public theorem strBytes_hexObj (ds : String) :
    PdfContentLex.strBytes? (hexObj ds) =
      some (match (ds.toList.map digitByte).foldl PdfContentLex.hexStep (ByteArray.empty, none) with
        | (out, some h) => out.push (UInt8.ofNat (h * 16))
        | (out, none) => out) := by
  rw [hexObj, PdfRead.strOf]
  unfold PdfContentLex.strBytes?
  dsimp only
  rw [ite_eq_left]
  · unfold PdfContentLex.hexBody
    rw [← Array.foldl_toList, Array.toList_extract]
    simp only [ByteArray.size, List.size_toArray, List.length_map, List.length_cons,
      List.length_append, List.extract, List.map_cons, List.map_append, List.map_nil, List.drop_one,
      List.cons_append, List.tail_cons, List.length_nil]
    rw [List.take_left' (by simp)]
    simp only [List.map_map]
    rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq, ByteArray.size, List.size_toArray,
      List.length_map, List.length_cons, List.length_append]
    refine ⟨by omega, rfl⟩

theorem bytes_two (x y : UInt8) : (((ByteArray.empty.push x).push y).data.toList) = [x, y] := rfl

/-- A glyph's code reads back from its four digits. -/
theorem codeOf_digits4 (g : Nat) :
    PdfFont.codeOf (hexObj (Hex.digits true 4 g)) = some (g % 65536, 2) := by
  unfold PdfFont.codeOf
  rw [strBytes_hexObj, hexStep_digits4]
  show some ((((ByteArray.empty.push (UInt8.ofNat (g / 256 % 256))).push
    (UInt8.ofNat (g % 256))).data.foldl (fun a x => a * 256 + x.toNat) 0, 2)) = _
  rw [← Array.foldl_toList, bytes_two]
  simp only [List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat', Option.some.injEq, Prod.mk.injEq,
    and_true]
  omega

theorem char_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at this
  exact this

/-- A character's UTF-16BE units read back as the character. -/
theorem utf16_utf16Hex (c : Char) :
    (PdfContentLex.strBytes? (hexObj (PdfRead.utf16Hex c))).map PdfFont.utf16 = some (String.singleton c) := by
  have hv := char_valid c
  unfold PdfRead.utf16Hex
  dsimp only
  split
  · next hlt =>
    rw [strBytes_hexObj, hexStep_digits4]
    simp only [Option.map_some, Option.some.injEq]
    unfold PdfFont.utf16
    rw [bytes_two, PdfFont.utf16Into.eq_def]
    simp only [UInt8.toNat_ofNat']
    rw [PdfFont.utf16Into.eq_def]
    simp only [PdfFont.unit16]
    rw [ite_eq_right (by simp; omega)]
    have : (c.toNat / 256 % 256 % 256 * 256 + c.toNat % 256 % 256) = c.toNat := by omega
    rw [this, Char.ofNat_toNat]
    rfl
  · next hge =>
    rw [strBytes_hexObj, String.toList_append, List.map_append, List.foldl_append,
      hexStep_digits4, hexStep_digits4]
    simp only [Option.map_some, Option.some.injEq]
    unfold PdfFont.utf16
    have hb : ((((ByteArray.empty.push (UInt8.ofNat ((0xD800 + (c.toNat - 0x10000) / 1024) / 256 % 256))).push
        (UInt8.ofNat ((0xD800 + (c.toNat - 0x10000) / 1024) % 256))).push
        (UInt8.ofNat ((0xDC00 + (c.toNat - 0x10000) % 1024) / 256 % 256))).push
        (UInt8.ofNat ((0xDC00 + (c.toNat - 0x10000) % 1024) % 256))).data.toList =
        [UInt8.ofNat ((0xD800 + (c.toNat - 0x10000) / 1024) / 256 % 256),
          UInt8.ofNat ((0xD800 + (c.toNat - 0x10000) / 1024) % 256),
          UInt8.ofNat ((0xDC00 + (c.toNat - 0x10000) % 1024) / 256 % 256),
          UInt8.ofNat ((0xDC00 + (c.toNat - 0x10000) % 1024) % 256)] := rfl
    rw [hb, PdfFont.utf16Into.eq_def]
    simp only [UInt8.toNat_ofNat']
    rw [ite_eq_left (by simp; omega)]
    rw [PdfFont.utf16Into.eq_def]
    simp only
    have : 0x10000 + ((0xD800 + (c.toNat - 0x10000) / 1024) / 256 % 256 % 256 * 256 +
        (0xD800 + (c.toNat - 0x10000) / 1024) % 256 % 256 - 0xD800) * 1024 +
        ((0xDC00 + (c.toNat - 0x10000) % 1024) / 256 % 256 % 256 * 256 +
        (0xDC00 + (c.toNat - 0x10000) % 1024) % 256 % 256 - 0xDC00) = c.toNat := by omega
    rw [this, Char.ofNat_toNat]
    rfl

/-! ### The reader's pass over the tokens -/

theorem uniStep_val (s : PdfFont.UniSt) (o : Obj) (h : s.mode = 0) : PdfFont.uniStep s (.val o) = s := by
  simp [PdfFont.uniStep, h]

theorem uniStep_val_open (s : PdfFont.UniSt) (o : Obj) (h : s.mode ≠ 0) :
    PdfFont.uniStep s (.val o) = { s with args := s.args.push o } := by
  simp [PdfFont.uniStep, h]

theorem uniStep_quiet (s : PdfFont.UniSt) (n : String) (h1 : n ≠ "beginbfchar")
    (h2 : n ≠ "beginbfrange") (h3 : n ≠ "endbfchar") (h4 : n ≠ "endbfrange") :
    PdfFont.uniStep s (.op n) = s := by
  unfold PdfFont.uniStep
  split <;> simp_all

/-- A token the reader's pass leaves alone outside a section. -/
def Quiet : Tok → Prop
  | .val _ => True
  | .op n => n ≠ "beginbfchar" ∧ n ≠ "beginbfrange" ∧ n ≠ "endbfchar" ∧ n ≠ "endbfrange"
  | .inline _ _ => False

theorem foldl_quiet (ts : List Tok) (hq : ∀ t ∈ ts, Quiet t) (s : PdfFont.UniSt) (h : s.mode = 0) :
    ts.foldl PdfFont.uniStep s = s := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    rw [List.foldl_cons]
    have ht : PdfFont.uniStep s t = s := by
      have := hq t (by simp)
      cases t with
      | val o => exact uniStep_val s o h
      | op n => exact uniStep_quiet s n this.1 this.2.1 this.2.2.1 this.2.2.2
      | inline _ _ => exact absurd this (by simp [Quiet])
    rw [ht]
    exact ih (fun u hu => hq u (by simp [hu]))

theorem cmapHead_quiet : ∀ t ∈ cmapHead.map (·.1), Quiet t := by
  intro t ht
  simp only [cmapHead, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (subst h; simp [Quiet])

theorem cmapTail_quiet : ∀ t ∈ cmapTail.map (·.1), Quiet t := by
  intro t ht
  simp only [cmapTail, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h | h | h | h | h <;> (subst h; simp [Quiet])

theorem foldl_vals (os : List Obj) (s : PdfFont.UniSt) (h : s.mode ≠ 0) :
    (os.map Tok.val).foldl PdfFont.uniStep s = { s with args := s.args ++ os.toArray } := by
  induction os generalizing s with
  | nil => simp
  | cons o rest ih =>
    rw [List.map_cons, List.foldl_cons, uniStep_val_open s o h, ih _ (by simpa using h)]
    congr 1
    apply Array.ext'
    simp

/-- A painted glyph's mapping, its code to its character. -/
def insertPair (m : Std.HashMap Nat String) (p : Nat × Char) : Std.HashMap Nat String :=
  m.insert p.1 (String.singleton p.2)

/-- One pair's two strings. -/
def pairObjs (p : Nat × Char) : List Obj :=
  [hexObj (Hex.digits true 4 p.1), hexObj (PdfRead.utf16Hex p.2)]

theorem bfchars_pairs (chunk : List (Nat × Char)) (hg : ∀ p ∈ chunk, p.1 < 65536)
    (m : Std.HashMap Nat String) :
    PdfFont.bfchars (chunk.flatMap pairObjs) m = chunk.foldl insertPair m := by
  induction chunk generalizing m with
  | nil => simp [PdfFont.bfchars]
  | cons p rest ih =>
    simp only [List.flatMap_cons, pairObjs, List.cons_append, List.nil_append, List.foldl_cons]
    rw [PdfFont.bfchars, codeOf_digits4]
    have hu := utf16_utf16Hex p.2
    cases hb : PdfContentLex.strBytes? (hexObj (PdfRead.utf16Hex p.2)) with
    | none => rw [hb] at hu; simp at hu
    | some dst =>
      rw [hb] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      simp only [hu, Nat.mod_eq_of_lt (hg p (by simp))]
      exact ih (fun q hq => hg q (by simp [hq])) _

theorem section_toks (chunk : List (Nat × Char)) :
    (bfcharSection chunk).map (·.1) =
      [.val (.int chunk.length), .op "beginbfchar"] ++ (chunk.flatMap pairObjs).map Tok.val ++
        [.op "endbfchar"] := by
  simp only [bfcharSection, List.map_append, List.map_cons, List.map_nil, List.map_flatMap]
  simp [bfcharPair, pairObjs]

theorem foldl_section (chunk : List (Nat × Char)) (hg : ∀ p ∈ chunk, p.1 < 65536)
    (s : PdfFont.UniSt) (h : s.mode = 0) :
    (((bfcharSection chunk).map (·.1)).foldl PdfFont.uniStep s).mode = 0 ∧
      (((bfcharSection chunk).map (·.1)).foldl PdfFont.uniStep s).m = chunk.foldl insertPair s.m := by
  rw [section_toks, List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, uniStep_val s _ h]
  rw [show PdfFont.uniStep s (.op "beginbfchar") = { s with mode := 1, args := #[] } by
    simp [PdfFont.uniStep]]
  rw [foldl_vals _ _ (by simp)]
  refine ⟨by simp [PdfFont.uniStep], ?_⟩
  simp only [PdfFont.uniStep, Array.toList_append, List.nil_append]
  exact bfchars_pairs chunk hg s.m

theorem chunksOf_flatten {α : Type} (n : Nat) : ∀ (l : List α), (chunksOf n l).flatten = l
  | [] => by rw [chunksOf]; rfl
  | x :: xs => by
    rw [chunksOf, List.flatten_cons, chunksOf_flatten n ((x :: xs).drop (max n 1)), List.take_append_drop]
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem chunksOf_mem {α : Type} (n : Nat) : ∀ (l : List α) (c : List α),
    c ∈ chunksOf n l → ∀ x ∈ c, x ∈ l
  | [], c, h => by rw [chunksOf] at h; simp at h
  | x :: xs, c, h => by
    rw [chunksOf, List.mem_cons] at h
    rcases h with rfl | h
    · intro y hy; exact List.mem_of_mem_take hy
    · intro y hy; exact List.mem_of_mem_drop (chunksOf_mem n _ c h y hy)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem foldl_sections (cs : List (List (Nat × Char))) (hg : ∀ c ∈ cs, ∀ p ∈ c, p.1 < 65536)
    (s : PdfFont.UniSt) (h : s.mode = 0) :
    ((cs.flatMap bfcharSection).map (·.1) |>.foldl PdfFont.uniStep s).mode = 0 ∧
      ((cs.flatMap bfcharSection).map (·.1) |>.foldl PdfFont.uniStep s).m = cs.flatten.foldl insertPair s.m := by
  induction cs generalizing s with
  | nil => exact ⟨h, rfl⟩
  | cons c rest ih =>
    rw [List.flatMap_cons, List.map_append, List.foldl_append]
    obtain ⟨h1, h2⟩ := foldl_section c (hg c (by simp)) s h
    obtain ⟨h3, h4⟩ := ih (fun d hd => hg d (by simp [hd])) _ h1
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.flatten_cons, List.foldl_append]

/-- The reader's mappings of the writer's CMap: each glyph's code to its character, in order. -/
theorem toUnicode_toUnicodeCMap (used : Array (Nat × Char)) (hg : ∀ p ∈ used, p.1 < 65536) :
    PdfFont.toUnicode (toUnicodeCMap used) = used.toList.foldl insertPair {} := by
  unfold PdfFont.toUnicode
  rw [scan_toUnicodeCMap, ← Array.foldl_toList, List.toList_toArray]
  unfold cmapToks
  rw [List.map_append, List.map_append, List.foldl_append, List.foldl_append,
    foldl_quiet _ cmapHead_quiet _ rfl]
  have hc := chunksOf_mem 100 used.toList
  obtain ⟨h1, h2⟩ := foldl_sections (chunksOf 100 used.toList)
    (fun c hcm p hp => hg p (by simpa using hc c hcm p hp)) ⟨{}, 0, #[]⟩ rfl
  rw [foldl_quiet _ cmapTail_quiet _ h1, h2, chunksOf_flatten 100]

/-! ### One character per code -/

theorem foldl_insertPair_get (l : List (Nat × Char)) (hnd : (l.map (·.1)).Nodup)
    (m : Std.HashMap Nat String) (g : Nat) :
    (l.foldl insertPair m)[g]? = match l.find? (·.1 == g) with
      | some p => some (String.singleton p.2)
      | none => m[g]? := by
  induction l generalizing m with
  | nil => rfl
  | cons p rest ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.mp hnd).2]
    have hp : p.1 ∉ rest.map (·.1) := (List.nodup_cons.mp (by simpa using hnd)).1
    simp only [List.find?_cons, insertPair, Std.HashMap.getElem?_insert]
    by_cases hg : p.1 = g
    · subst hg
      have : rest.find? (·.1 == p.1) = none := by
        rw [List.find?_eq_none]
        intro q hq hqe
        exact hp (List.mem_map.mpr ⟨q, hq, by simpa using hqe⟩)
      simp [this]
    · have hg' : (p.1 == g) = false := by simpa using hg
      cases rest.find? (·.1 == g) <;> simp [hg']

/-- A row of marks as the glyphs it marks, each with its character, from index `i`. -/
theorem zipIdx_find (l : List (Option Char)) (i g : Nat) :
    ((l.zipIdx i).filterMap fun (c?, k) => c?.map (k, ·)).find? (·.1 == g) =
      if i ≤ g then (l[g - i]?.join).map (g, ·) else none := by
  induction l generalizing i with
  | nil => simp
  | cons c rest ih =>
    rw [List.zipIdx_cons, List.filterMap_cons]
    cases c with
    | none =>
      simp only [Option.map_none]
      rw [ih]
      by_cases h : i = g
      · subst h
        simp only [show ¬ (i + 1 ≤ i) by omega, ite_false, Nat.le_refl, ite_true, Nat.sub_self,
          List.getElem?_cons_zero]
        rfl
      · by_cases h2 : i + 1 ≤ g
        · have : g - i = (g - (i + 1)) + 1 := by omega
          simp [h2, show i ≤ g by omega, this]
        · simp [h2, show ¬ i ≤ g by omega]
    | some ch =>
      simp only [Option.map_some, List.find?_cons]
      by_cases h : i = g
      · subst h; simp
      · have hb : (i == g) = false := by simpa using h
        simp only [hb]
        rw [ih]
        by_cases h2 : i + 1 ≤ g
        · have : g - i = (g - (i + 1)) + 1 := by omega
          simp [h2, show i ≤ g by omega, this]
        · simp [h2, show ¬ i ≤ g by omega]

theorem zipIdx_keys_lt (l : List (Option Char)) (i : Nat) :
    ∀ p ∈ (l.zipIdx i).filterMap (fun (c?, k) => c?.map (k, ·)), i ≤ p.1 ∧ p.1 < i + l.length := by
  induction l generalizing i with
  | nil => simp
  | cons c rest ih =>
    intro p hp
    rw [List.zipIdx_cons, List.filterMap_cons] at hp
    cases c with
    | none =>
      have := ih (i + 1) p hp
      simp only [List.length_cons]; omega
    | some ch =>
      simp only [Option.map_some, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · have := ih (i + 1) p hp
        simp only [List.length_cons]; omega

theorem zipIdx_nodup (l : List (Option Char)) (i : Nat) :
    (((l.zipIdx i).filterMap fun (c?, k) => c?.map (k, ·)).map (·.1)).Nodup := by
  induction l generalizing i with
  | nil => simp
  | cons c rest ih =>
    rw [List.zipIdx_cons, List.filterMap_cons]
    cases c with
    | none => exact ih (i + 1)
    | some ch =>
      simp only [Option.map_some, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih (i + 1)⟩
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      have := zipIdx_keys_lt rest (i + 1) q hq
      omega

/-- A face's marks at a glyph: its row's entry, `none` where the face or glyph is out of range. -/
def markAt (seen : Array (Array (Option Char))) (k g : Nat) : Option (Option Char) :=
  (seen[k]?).bind (·[g]?)

theorem markOne_markAt (seen : Array (Array (Option Char))) (p : Nat × Nat × Char) (k g : Nat) :
    markAt (markOne seen p) k g =
      if p.1 = k ∧ p.2.1 = g ∧ markAt seen k g = some none then some (some p.2.2) else markAt seen k g := by
  unfold markAt markOne
  rw [Array.getElem?_modify]
  by_cases hk : p.1 = k
  · subst hk
    simp only [ite_true, true_and]
    cases hr : seen[p.1]? with
    | none => simp
    | some row =>
      simp only [Option.map_some, Option.bind_some]
      split
      · next hlt =>
        split
        · next hn =>
          rw [Array.getElem?_set]
          by_cases hg : p.2.1 = g
          · subst hg
            have : row[p.2.1]? = some none := by
              rw [Array.getElem?_eq_getElem hlt]; simpa using hn
            simp [this]
          · simp [hg]
        · next hn =>
          by_cases hg : p.2.1 = g
          · subst hg
            have : row[p.2.1]? ≠ some none := by
              rw [Array.getElem?_eq_getElem hlt]; simpa using hn
            simp [this]
          · simp [hg]
      · next hlt =>
        by_cases hg : p.2.1 = g
        · subst hg
          have : row[p.2.1]? = none := Array.getElem?_eq_none (by omega)
          simp [this]
        · simp [hg]
  · simp [hk]

/-- Marking in `painted`'s order leaves each glyph's first character. -/
theorem foldl_markOne (l : List (Nat × Nat × Char)) (seen : Array (Array (Option Char))) (k g : Nat) :
    markAt (l.foldl markOne seen) k g =
      if markAt seen k g = some none then
        some ((l.find? fun p => p.1 == k && p.2.1 == g).map (·.2.2))
      else markAt seen k g := by
  induction l generalizing seen with
  | nil => split <;> simp_all
  | cons p rest ih =>
    rw [List.foldl_cons, ih, markOne_markAt, List.find?_cons]
    by_cases hp : p.1 = k ∧ p.2.1 = g
    · obtain ⟨h1, h2⟩ := hp
      by_cases hs : markAt seen k g = some none
      · simp [h1, h2, hs]
      · simp only [h1, h2, hs]
        simp only [and_false, ite_false, ite_eq_right_iff]
        intro h
        exact absurd h hs
    · have hb : (p.1 == k && p.2.1 == g) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        by_cases h1 : p.1 = k
        · exact Or.inr (fun h2 => hp ⟨h1, h2⟩)
        · exact Or.inl h1
      have : ¬ (p.1 = k ∧ p.2.1 = g ∧ markAt seen k g = some none) := fun h => hp ⟨h.1, h.2.1⟩
      simp only [this, ite_false, hb]

theorem markOne_size (seen : Array (Array (Option Char))) (p : Nat × Nat × Char) (k : Nat) :
    ((markOne seen p)[k]?).map Array.size = (seen[k]?).map Array.size := by
  unfold markOne
  rw [Array.getElem?_modify]
  split
  · next h =>
    subst h
    cases seen[p.1]? with
    | none => rfl
    | some row =>
      simp only [Option.map_some, Option.some.injEq]
      split
      · split <;> simp
      · rfl
  · rfl

theorem foldl_markOne_size (l : List (Nat × Nat × Char)) (seen : Array (Array (Option Char))) (k : Nat) :
    ((l.foldl markOne seen)[k]?).map Array.size = (seen[k]?).map Array.size := by
  induction l generalizing seen with
  | nil => rfl
  | cons p rest ih => rw [List.foldl_cons, ih, markOne_size]

theorem markSeg_painted (shaped : Array (Option (Gfx.Figure Gfx.Shaped)))
    (seen : Array (Array (Option Char))) (s : Seg) :
    markSeg shaped seen s = (segPainted shaped s).foldl markOne seen := by
  cases s
  case run idx _ _ _ glyphs _ _ _ _ _ _ =>
    simp only [markSeg, segPainted, List.foldl_map]
    rw [← Array.foldl_toList]
  case image store _ _ _ _ _ =>
    cases store with
    | none => rfl
    | some k =>
      simp only [markSeg, segPainted]
      cases (shaped[k]?).join <;> rfl
  all_goals rfl

/-- Marking walks the glyphs in `painted`'s order. -/
theorem markUsed_painted (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) :
    markUsed fs pages shaped =
      (painted pages shaped).foldl markOne (fs.fonts.map fun f => Array.replicate f.numGlyphs none) := by
  unfold markUsed painted
  rw [← Array.foldl_toList, List.foldl_flatMap]
  congr 1
  funext seen p
  rw [← Array.foldl_toList, List.foldl_flatMap]
  congr 1
  funext seen l
  rw [← Array.foldl_toList, List.foldl_flatMap]
  congr 1
  funext seen s
  exact markSeg_painted shaped seen s

/-- A face's used glyph `g`, with the first character `painted` lists a glyph `g` of it with. -/
theorem usedAll_find (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) (k g : Nat) (hk : k < fs.fonts.size) :
    ((usedAll fs pages shaped)[k]?.getD #[]).toList.find? (·.1 == g) =
      if g < fs.fonts[k].numGlyphs then
        ((painted pages shaped).find? fun p => p.1 == k && p.2.1 == g).map fun p => (g, p.2.2)
      else none := by
  have hsz : k < (usedAll fs pages shaped).size := by rw [usedAll_size_exact]; exact hk
  rw [Array.getElem?_eq_getElem hsz, Option.getD_some]
  simp only [usedAll, Array.getElem_map, Array.getElem_range]
  rw [Array.toList_filterMap, Array.toList_zipIdx, zipIdx_find]
  simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  have hm := foldl_markOne (painted pages shaped) (fs.fonts.map fun f => Array.replicate f.numGlyphs none) k g
  rw [← markUsed_painted] at hm
  have h0 : markAt (fs.fonts.map fun f => Array.replicate f.numGlyphs none) k g =
      if g < fs.fonts[k].numGlyphs then some none else none := by
    simp [markAt, Array.getElem?_map, Array.getElem?_eq_getElem hk, Array.getElem?_replicate]
  rw [h0] at hm
  unfold markAt at hm
  split
  · next hg =>
    simp only [hg, ite_true] at hm
    cases hr : (markUsed fs pages shaped)[k]? with
    | none => rw [hr] at hm; simp at hm
    | some row =>
      rw [hr] at hm
      simp only [Option.bind_some] at hm
      simp only [Option.getD_some, Array.getElem?_toList, hm, Option.join_some]
      cases (painted pages shaped).find? (fun p => p.1 == k && p.2.1 == g) <;> rfl
  · next hg =>
    simp only [hg, ite_false] at hm
    cases hr : (markUsed fs pages shaped)[k]? with
    | none => simp
    | some row =>
      rw [hr] at hm
      simp only [Option.bind_some] at hm
      simp [Array.getElem?_toList, hm]

/-- Every glyph a face marks is one of its glyphs. -/
theorem usedAll_lt (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) (k : Nat) (hk : k < fs.fonts.size) :
    ∀ p ∈ (usedAll fs pages shaped)[k]?.getD #[], p.1 < fs.fonts[k].numGlyphs := by
  have hsz : k < (usedAll fs pages shaped).size := by rw [usedAll_size_exact]; exact hk
  rw [Array.getElem?_eq_getElem hsz, Option.getD_some]
  simp only [usedAll, Array.getElem_map, Array.getElem_range]
  have hs := foldl_markOne_size (painted pages shaped) (fs.fonts.map fun f => Array.replicate f.numGlyphs none) k
  rw [← markUsed_painted] at hs
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem hk, Option.map_some, Array.size_replicate] at hs
  have hrow : ((markUsed fs pages shaped)[k]?.getD #[]).size = fs.fonts[k].numGlyphs := by
    cases hr : (markUsed fs pages shaped)[k]? with
    | none => rw [hr] at hs; simp at hs
    | some row => rw [hr] at hs; simpa using hs
  intro p hp
  rw [← Array.mem_toList_iff, Array.toList_filterMap, Array.toList_zipIdx] at hp
  have h := zipIdx_keys_lt _ 0 p hp
  rw [Array.length_toList, hrow] at h
  omega

theorem usedAll_nodup (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) (k : Nat) :
    (((usedAll fs pages shaped)[k]?.getD #[]).toList.map (·.1)).Nodup := by
  by_cases hsz : k < (usedAll fs pages shaped).size
  · rw [Array.getElem?_eq_getElem hsz, Option.getD_some]
    simp only [usedAll, Array.getElem_map, Array.getElem_range]
    rw [Array.toList_filterMap, Array.toList_zipIdx]
    exact zipIdx_nodup _ 0
  · rw [Array.getElem?_eq_none (by omega)]
    exact List.nodup_nil

/-- The ToUnicode CMap the file embeds for face `k`, whose glyph count fits the two-byte codes,
reads back as each code to the first character `painted` sets its glyph for, else as nothing. -/
public theorem toUnicode_glyphs_exact (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) (k g : Nat) (hk : k < fs.fonts.size)
    (hn : fs.fonts[k].numGlyphs ≤ 65536) :
    (PdfFont.toUnicode (faceCMap (usedAll fs pages shaped) k))[g]? =
      if g < fs.fonts[k].numGlyphs then
        ((painted pages shaped).find? fun p => p.1 == k && p.2.1 == g).map fun p =>
          String.singleton p.2.2
      else none := by
  have hlt := usedAll_lt fs pages shaped k hk
  rw [faceCMap, toUnicode_toUnicodeCMap _ (fun p hp => by have := hlt p hp; omega),
    foldl_insertPair_get _ (usedAll_nodup fs pages shaped k), usedAll_find fs pages shaped k g hk]
  by_cases hg : g < fs.fonts[k].numGlyphs
  · simp only [hg, ite_true]
    cases (painted pages shaped).find? (fun p => p.1 == k && p.2.1 == g) <;> simp
  · simp [hg]

end LeanTex.Core.Pdf
