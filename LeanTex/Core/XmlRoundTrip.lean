module

public import LeanTex.Core.Xml
import all LeanTex.Core.Xml
public import LeanTex.Core.XmlContract
import Std.Data.HashSet.Lemmas
import all Init.Data.Repr

/-!
# The XML writer, read back

The reader reads a rendered tree back as it stands (`parse_render_id`): a
tree whose root is an element, whose names are ASCII names within the name
budget, whose attributes are named once in each element, whose text and
attribute values are characters XML admits within the text budget — no text
node empty and no two adjacent — and whose spelling lies within the size,
depth and node budgets.

`render` writes ASCII — a literal character as itself, every other as a
decimal reference — so the proof reads the spelling a character a byte, and
follows the reader token by token: a start tag, an end tag, a run of literal
text and a reference are each one forward step, and a tree's spelling is the
steps of its tags around its kids'. A round trip is a claim about what the
reader's loops return, which no invariant sees (`LeanTex.Core.Loop`), so each
loop is read by its progress: a body that ignores its index, stepped a
counted number of times (`loopN`, `loopE`, `Reach`).
-/

namespace LeanTex.Core.Xml

/-! ## An ASCII spelling, byte for character -/

/-- Characters of the first 128 code points. -/
private def Ascii (l : List Char) : Prop := ∀ c ∈ l, c.toNat < 128

/-- The bytes of an ASCII character list, one each. -/
private def bytesOf (l : List Char) : ByteArray := (l.map fun c => UInt8.ofNat c.toNat).toByteArray

private theorem size_bytesOf (l : List Char) : (bytesOf l).size = l.length := by
  simp [bytesOf]

private theorem at?_bytesOf (l : List Char) (i : Nat) (hl : Ascii l) :
    at? (bytesOf l) i = (l[i]?.map Char.toNat).getD 256 := by
  unfold at? bytesOf
  by_cases h : i < l.length
  · have hi : i < (l.map fun c => UInt8.ofNat c.toNat).toByteArray.size := by simp [h]
    rw [getElem?_pos ((l.map fun c => UInt8.ofNat c.toNat).toByteArray) i hi]
    simp only [List.getElem_toByteArray, List.getElem_map, Option.map_some, Option.getD_some,
      List.getElem?_eq_getElem h]
    have := hl _ (List.getElem_mem h)
    simp only [UInt8.toNat_ofNat']
    omega
  · have hi : ¬ i < (l.map fun c => UInt8.ofNat c.toNat).toByteArray.size := by simpa using h
    rw [getElem?_neg ((l.map fun c => UInt8.ofNat c.toNat).toByteArray) i hi]
    simp [List.getElem?_eq_none (by omega : l.length ≤ i)]

private theorem utf8EncodeChar_ascii (c : Char) (h : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  have : c.val.toNat ≤ 127 := by
    have : c.toNat = c.val.toNat := rfl
    omega
  simp only [this, ↓reduceIte]
  rfl

private theorem utf8Encode_ascii (l : List Char) (hl : Ascii l) : l.utf8Encode = bytesOf l := by
  unfold List.utf8Encode bytesOf
  congr 1
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, List.map_cons]
    rw [utf8EncodeChar_ascii c (hl c (by simp)), ih (fun d hd => hl d (by simp [hd]))]
    rfl

private theorem toUTF8_ascii (s : String) (hl : Ascii s.toList) : s.toUTF8 = bytesOf s.toList := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, utf8Encode_ascii _ hl]

private theorem fromUTF8?_bytesOf (l : List Char) (hl : Ascii l) :
    String.fromUTF8? (bytesOf l) = some (String.ofList l) := by
  have hv : (bytesOf l).IsValidUTF8 := ⟨l, (utf8Encode_ascii l hl).symm⟩
  unfold String.fromUTF8?
  simp only [hv, ↓reduceDIte]
  congr 1
  apply String.toByteArray_inj.mp
  simp [String.fromUTF8, utf8Encode_ascii l hl]

private theorem validateUTF8_bytesOf (l : List Char) (hl : Ascii l) : (bytesOf l).validateUTF8 = true :=
  ByteArray.validateUTF8_eq_true_iff.mpr ⟨l, (utf8Encode_ascii l hl).symm⟩

/-! ## Loops whose body ignores its index -/

/-- `n` steps of a loop body that ignores its index. -/
private def loopN {β : Type} (g : β → ForInStep β) : Nat → β → β
  | 0, b => b
  | n + 1, b => match g b with
    | .done b' => b'
    | .yield b' => loopN g n b'

private theorem forIn_range'_loopN {β : Type} (g : β → ForInStep β) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ x b, f x b = pure (g b)) (s n : Nat) (b : β) :
    (forIn (List.range' s n) b f : Id β).run = loopN g n b := by
  induction n generalizing s b with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons, hf]
    simp only [loopN]
    cases g b with
    | done b' => rfl
    | yield b' => exact ih (s + 1) b'

private theorem forIn_range_loopN {β : Type} (g : β → ForInStep β) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ x b, f x b = pure (g b)) (n : Nat) (b : β) :
    (forIn [:n] b f : Id β).run = loopN g n b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [this]
  exact forIn_range'_loopN g f hf _ n b

/-! ## Scanning a run -/

/-- The scan's step: one more byte while `pred` holds. -/
private def scanStep (b : ByteArray) (pred : Nat → Bool) (j : Nat) : ForInStep Nat :=
  if pred (at? b j) then .yield (j + 1) else .done j

private theorem scanWhile_loopN (b : ByteArray) (pred : Nat → Bool) (i : Nat) :
    scanWhile b pred i = loopN (scanStep b pred) (b.size + 1) i := by
  unfold scanWhile
  exact forIn_range_loopN (scanStep b pred) _ (fun _ j => by
    simp only [scanStep]; split <;> rfl) _ i

/-- The run of characters from `l` that `pred` reads as bytes. -/
private def runLen (pred : Nat → Bool) (l : List Char) : Nat := (l.takeWhile fun c => pred c.toNat).length

private theorem loopN_scan (l : List Char) (hl : Ascii l) (pred : Nat → Bool) (h256 : pred 256 = false) :
    ∀ (n j : Nat), runLen pred (l.drop j) < n →
      loopN (scanStep (bytesOf l) pred) n j = j + runLen pred (l.drop j) := by
  intro n
  induction n with
  | zero => intro j h; omega
  | succ n ih =>
    intro j h
    simp only [loopN, scanStep]
    rw [at?_bytesOf l j hl]
    by_cases hj : j < l.length
    · rw [List.getElem?_eq_getElem hj]
      simp only [Option.map_some, Option.getD_some]
      have hd : l.drop j = l[j] :: l.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
      by_cases hp : pred l[j].toNat = true
      · simp only [hp, ↓reduceIte]
        have hr : runLen pred (l.drop j) = 1 + runLen pred (l.drop (j + 1)) := by
          simp only [runLen, hd, List.takeWhile_cons, hp, ↓reduceIte, List.length_cons]
          omega
        rw [ih (j + 1) (by omega), hr]
        omega
      · have hp' : pred l[j].toNat = false := by simpa using hp
        simp only [hp', Bool.false_eq_true, ↓reduceIte]
        simp only [runLen, hd, List.takeWhile_cons, hp', Bool.false_eq_true, ↓reduceIte,
          List.length_nil, Nat.add_zero]
    · rw [List.getElem?_eq_none (by omega)]
      simp only [Option.map_none, Option.getD_none, h256, Bool.false_eq_true, ↓reduceIte]
      simp [runLen, List.drop_eq_nil_of_le (by omega : l.length ≤ j)]

private theorem runLen_le (pred : Nat → Bool) (l : List Char) : runLen pred l ≤ l.length := by
  unfold runLen
  exact (List.takeWhile_sublist _).length_le

/-- **A scan over an ASCII spelling stops at the end of its run.** -/
private theorem scanWhile_bytesOf (l : List Char) (hl : Ascii l) (pred : Nat → Bool) (h256 : pred 256 = false)
    (j : Nat) : scanWhile (bytesOf l) pred j = j + runLen pred (l.drop j) := by
  rw [scanWhile_loopN, size_bytesOf]
  apply loopN_scan l hl pred h256
  have := runLen_le pred (l.drop j)
  simp at this
  omega

private theorem extract_bytesOf (l : List Char) (i j : Nat) :
    (bytesOf l).extract i j = bytesOf ((l.drop i).take (j - i)) := by
  apply ByteArray.ext
  simp [bytesOf, ByteArray.data_extract, List.data_toByteArray, List.map_drop, List.map_take]

private theorem ascii_sub (l : List Char) (hl : Ascii l) (i k : Nat) : Ascii ((l.drop i).take k) :=
  fun c hc => hl c (List.mem_of_mem_drop (List.mem_of_mem_take hc))

/-- **A slice of an ASCII spelling is its characters.** -/
private theorem slice_bytesOf (l : List Char) (hl : Ascii l) (i j : Nat) :
    slice (bytesOf l) i j = String.ofList ((l.drop i).take (j - i)) := by
  unfold slice
  rw [extract_bytesOf, fromUTF8?_bytesOf _ (ascii_sub l hl i (j - i))]
  rfl

/-! ## The spelling as characters -/

/-- A character's reference, as characters. -/
private def refL (c : Char) : List Char := '&' :: '#' :: (Nat.toDigits 10 c.toNat ++ [';'])

/-- A character's spelling: itself when literal, else its reference. -/
private def pieceL (c : Char) : List Char := if literal c then [c] else refL c

/-- Characters, canonically spelled. -/
private def escL (s : List Char) : List Char := s.flatMap pieceL

/-- An attribute list's spelling. -/
private def attrsL : List (String × String) → List Char
  | [] => []
  | (k, v) :: rest => ' ' :: (k.toList ++ ('=' :: '"' :: (escL v.toList ++ ('"' :: attrsL rest))))

mutual
/-- A node's spelling after `out`, as `renderOne` writes it. -/
private def nodeOn (out : List Char) : Node → List Char
  | .elem name attrs kids =>
    let out := out ++ '<' :: (name.toList ++ attrsL attrs.toList)
    if kids.isEmpty then out ++ ['/', '>']
    else kidsOn (out ++ ['>']) kids.toList ++ '<' :: '/' :: (name.toList ++ ['>'])
  | .text s => out ++ escL s.toList
/-- A list of nodes' spelling after `out`. -/
private def kidsOn (out : List Char) : List Node → List Char
  | [] => out
  | n :: rest => kidsOn (nodeOn out n) rest
end

/-- A node's spelling, as `render` writes it. -/
private def nodeL (n : Node) : List Char := nodeOn [] n

/-- A list of nodes' spelling. -/
private def kidsL (ks : List Node) : List Char := kidsOn [] ks

mutual
private theorem nodeOn_eq (out : List Char) (n : Node) : nodeOn out n = out ++ nodeL n := by
  cases n with
  | elem name attrs kids =>
    simp only [nodeL, nodeOn]
    split
    · simp
    · rw [kidsOn_eq _ kids.toList, kidsOn_eq _ kids.toList]
      simp
  | text s => simp [nodeL, nodeOn]
private theorem kidsOn_eq (out : List Char) (ks : List Node) : kidsOn out ks = out ++ kidsL ks := by
  match ks with
  | [] => simp [kidsL, kidsOn]
  | n :: rest =>
    simp only [kidsL, kidsOn]
    rw [kidsOn_eq _ rest, kidsOn_eq (nodeOn [] n) rest, nodeOn_eq out n, nodeOn_eq [] n]
    simp
end

private theorem nodeL_elem (name : String) (attrs : Array (String × String)) (kids : Array Node) :
    nodeL (.elem name attrs kids) =
      if kids.isEmpty then '<' :: (name.toList ++ (attrsL attrs.toList ++ ['/', '>']))
      else '<' :: (name.toList ++ (attrsL attrs.toList ++ ('>' :: (kidsL kids.toList ++
        ('<' :: '/' :: (name.toList ++ ['>'])))))) := by
  simp only [nodeL, nodeOn]
  split
  · simp
  · rw [kidsOn_eq]
    simp

private theorem nodeL_text (s : String) : nodeL (.text s) = escL s.toList := by
  simp [nodeL, nodeOn]

private theorem kidsL_nil : kidsL [] = [] := rfl

private theorem kidsL_cons (n : Node) (rest : List Node) : kidsL (n :: rest) = nodeL n ++ kidsL rest := by
  rw [kidsL, kidsOn, kidsOn_eq, nodeOn_eq, List.nil_append]

private theorem charRef_toList (c : Char) : (charRef c).toList = refL c := by
  simp [charRef, refL, String.toList_append]

private theorem escapeFold_toList (acc : String) (l : List Char) :
    (l.foldl (fun acc c => if literal c then acc.push c else acc ++ charRef c) acc).toList =
      acc.toList ++ escL l := by
  induction l generalizing acc with
  | nil => simp [escL]
  | cons c rest ih =>
    simp only [List.foldl_cons, escL, List.flatMap_cons]
    rw [ih]
    by_cases hc : literal c = true
    · simp [hc, pieceL, escL]
    · simp [hc, pieceL, escL, String.toList_append, charRef_toList]

private theorem escapeChars_toList (s : String) : (escapeChars s).toList = escL s.toList := by
  unfold escapeChars
  rw [String.foldl_eq_foldl_toList, escapeFold_toList]
  rfl

private theorem attrsFold_toList (attrs : List (String × String)) (o : String) :
    (attrs.foldl (fun o (kv : String × String) => o ++ " " ++ kv.1 ++ "=\"" ++ escapeChars kv.2 ++ "\"") o).toList =
      o.toList ++ attrsL attrs := by
  induction attrs generalizing o with
  | nil => simp [attrsL]
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp [ih, attrsL, String.toList_append, escapeChars_toList]

mutual
private theorem renderOne_nodeOn (out : String) (n : Node) :
    (renderOne out n).toList = nodeOn out.toList n := by
  cases n with
  | elem name attrs kids =>
    simp only [renderOne, nodeOn]
    have hf := attrsFold_toList attrs.toList (out ++ "<" ++ name)
    simp only [← Array.foldl_toList]
    split
    · simp only [String.toList_append, hf]
      simp
    · simp only [String.toList_append]
      rw [renderList_kidsOn, String.toList_append, hf]
      simp
  | text s => simp [renderOne, nodeOn, String.toList_append, escapeChars_toList]
private theorem renderList_kidsOn (out : String) (l : List Node) :
    (renderList out l).toList = kidsOn out.toList l := by
  match l with
  | [] => simp [renderList, kidsOn]
  | n :: rest => simp [renderList, kidsOn, renderList_kidsOn _ rest, renderOne_nodeOn out n]
end

private theorem renderOne_toList (out : String) (n : Node) :
    (renderOne out n).toList = out.toList ++ nodeL n := by
  rw [renderOne_nodeOn, nodeOn_eq]

/-! ## Decimal references -/

private theorem digitChar_toNat (n : Nat) (h : n < 10) : (Nat.digitChar n).toNat = 48 + n := by
  match n, h with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl

private theorem toDigits_digit (n : Nat) : ∀ d ∈ Nat.toDigits 10 n, 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by
  intro d hd
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨h1, h2⟩ := this
  constructor
  · have : ('0' : Char).toNat ≤ d.toNat := h1
    simpa using this
  · have : d.toNat ≤ ('9' : Char).toNat := h2
    simpa using this

private theorem foldDigits (n : Nat) :
    (Nat.toDigits 10 n).foldl (fun v d => v * 10 + (d.toNat - 48)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · next h => simp [digitChar_toNat n h]
    · next h =>
      rw [List.foldl_append, ih (n / 10) (by omega)]
      simp [digitChar_toNat (n % 10) (Nat.mod_lt _ (by decide))]
      omega

private theorem toDigits_length_le (n : Nat) (h : n < 10000000) : (Nat.toDigits 10 n).length ≤ 7 := by
  have := (Nat.length_toDigits_le_iff (b := 10) (n := n) (k := 7) (by decide) (by decide)).mpr
  exact this (by simpa using h)

/-- The byte at `i + k` is the `k`-th character after `i`. -/
private theorem at?_drop (R : List Char) (hl : Ascii R) (i k : Nat) :
    at? (bytesOf R) (i + k) = (((R.drop i)[k]?).map Char.toNat).getD 256 := by
  rw [at?_bytesOf R _ hl, List.getElem?_drop]

private theorem at?_of_drop (R : List Char) (hl : Ascii R) (i : Nat) (c : Char) (rest : List Char)
    (h : R.drop i = c :: rest) : at? (bytesOf R) i = c.toNat := by
  have := at?_drop R hl i 0
  rw [Nat.add_zero, h] at this
  simpa using this

private theorem drop_succ_of (R : List Char) (i : Nat) (c : Char) (rest : List Char)
    (h : R.drop i = c :: rest) : R.drop (i + 1) = rest := by
  rw [← List.drop_drop, h]
  rfl

private theorem drop_append_of (R : List Char) (i : Nat) (a rest : List Char)
    (h : R.drop i = a ++ rest) : R.drop (i + a.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

private theorem runLen_append (pred : Nat → Bool) (a rest : List Char) (ha : ∀ c ∈ a, pred c.toNat = true)
    (hr : ∀ c ∈ rest.head?, pred c.toNat = false) : runLen pred (a ++ rest) = a.length := by
  unfold runLen
  induction a with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c more =>
      have := hr c (by simp)
      simp [this]
  | cons c more ih =>
    have hc := ha c (by simp)
    simp only [List.cons_append, List.takeWhile_cons, hc, ↓reduceIte, List.length_cons]
    rw [ih (fun d hd => ha d (by simp [hd]))]

/-- The value loop of a decimal reference over its digits. -/
private theorem refValue_fold (R : List Char) (hl : Ascii R) (d0 m : Nat) (v : Nat) (hm : d0 + m ≤ R.length) :
    List.foldl (fun v k => v * 10 + (hexVal (at? (bytesOf R) k)).getD 0) v (List.range' d0 m) =
      List.foldl (fun v (ch : Char) => v * 10 + (hexVal ch.toNat).getD 0) v ((R.drop d0).take m) := by
  induction m generalizing d0 v with
  | zero => simp
  | succ m ih =>
    have hd : d0 < R.length := by omega
    rw [List.range'_succ, List.foldl_cons, ih (d0 + 1) _ (by omega)]
    rw [List.drop_eq_getElem_cons hd, List.take_succ_cons, List.foldl_cons]
    rw [at?_bytesOf R d0 hl, List.getElem?_eq_getElem hd]
    simp

private theorem hexVal_digit (d : Char) (h : 48 ≤ d.toNat ∧ d.toNat ≤ 57) : (hexVal d.toNat).getD 0 = d.toNat - 48 := by
  unfold hexVal
  simp [h.1, h.2]

private theorem fold_digits_value (n : Nat) :
    List.foldl (fun v (ch : Char) => v * 10 + (hexVal ch.toNat).getD 0) 0 (Nat.toDigits 10 n) = n := by
  have heq : ∀ (l : List Char) (v : Nat), (∀ d ∈ l, 48 ≤ d.toNat ∧ d.toNat ≤ 57) →
      List.foldl (fun v (ch : Char) => v * 10 + (hexVal ch.toNat).getD 0) v l =
        List.foldl (fun v (d : Char) => v * 10 + (d.toNat - 48)) v l := by
    intro l
    induction l with
    | nil => simp
    | cons d rest ih =>
      intro v h
      simp only [List.foldl_cons]
      rw [hexVal_digit d (h d (by simp))]
      exact ih _ (fun x hx => h x (by simp [hx]))
  rw [heq _ 0 (toDigits_digit n), foldDigits]

/-- **A decimal reference reads back as its character.** -/
private theorem readReference_ref (R : List Char) (hl : Ascii R) (i : Nat) (c : Char) (rest : List Char)
    (hR : R.drop i = refL c ++ rest) (hc : xmlChar c.toNat = true) :
    readReference (bytesOf R) i = .ok (c, i + (refL c).length) := by
  have hds := toDigits_digit c.toNat
  have hne := @Nat.toDigits_ne_nil c.toNat 10
  obtain ⟨d, ds, hdd⟩ : ∃ d ds, Nat.toDigits 10 c.toNat = d :: ds := by
    cases h : Nat.toDigits 10 c.toNat with
    | nil => exact absurd h hne
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hR1 : R.drop (i + 1) = '#' :: (Nat.toDigits 10 c.toNat ++ (';' :: rest)) := by
    apply drop_succ_of R i '&'
    rw [hR]; simp [refL]
  have hR2 : R.drop (i + 2) = Nat.toDigits 10 c.toNat ++ (';' :: rest) := by
    have := drop_succ_of R (i + 1) '#' _ hR1
    simpa using this
  have h35 : at? (bytesOf R) (i + 1) = 35 := by
    rw [at?_of_drop R hl (i + 1) '#' _ hR1]; rfl
  have hxd : at? (bytesOf R) (i + 2) = d.toNat := by
    apply at?_of_drop R hl (i + 2) d (ds ++ ';' :: rest)
    rw [hR2, hdd]; rfl
  have hd := hds d (by rw [hdd]; simp)
  have hhex : (at? (bytesOf R) (i + 2) == 120) = false := by
    rw [hxd]; simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hscan : scanWhile (bytesOf R) (fun c => decide (48 ≤ c) && decide (c ≤ 57)) (i + 2) =
      i + 2 + (Nat.toDigits 10 c.toNat).length := by
    rw [scanWhile_bytesOf R hl _ (by decide), hR2, runLen_append]
    · intro x hx
      have := hds x hx
      simp [this.1, this.2]
    · intro x hx
      simp at hx
      subst hx
      decide
  have hsemi : at? (bytesOf R) (i + 2 + (Nat.toDigits 10 c.toNat).length) = 59 := by
    rw [at?_of_drop R hl _ ';' rest (drop_append_of R (i + 2) _ _ hR2)]; rfl
  have hlen : (Nat.toDigits 10 c.toNat).length ≤ 7 := by
    apply toDigits_length_le
    simp only [xmlChar, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  have hval : (forIn [i + 2 : i + 2 + (Nat.toDigits 10 c.toNat).length] 0 fun k (v : Nat) =>
      (pure (ForInStep.yield (v * 10 + (hexVal (at? (bytesOf R) k)).getD 0)) : Id (ForInStep Nat))).run =
      c.toNat := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hsz : ([i + 2 : i + 2 + (Nat.toDigits 10 c.toNat).length] : Std.Legacy.Range).size =
        (Nat.toDigits 10 c.toNat).length := by simp [Std.Legacy.Range.size]
    rw [hsz]
    have := List.idRun_forIn_yield_eq_foldl (List.range' (i + 2) (Nat.toDigits 10 c.toNat).length 1)
      (fun k v => (pure (v * 10 + (hexVal (at? (bytesOf R) k)).getD 0) : Id Nat)) 0
    simp only at this ⊢
    rw [show (fun k (v : Nat) => (pure (ForInStep.yield (v * 10 + (hexVal (at? (bytesOf R) k)).getD 0)) :
        Id (ForInStep Nat))) = (fun k v => ForInStep.yield <$> (pure (v * 10 + (hexVal (at? (bytesOf R) k)).getD 0) :
        Id Nat)) from rfl, this]
    simp only [Id.run_pure]
    have hfit : i + 2 + (Nat.toDigits 10 c.toNat).length ≤ R.length := by
      have := congrArg List.length hR2
      simp only [List.length_drop, List.length_append, List.length_cons] at this
      omega
    rw [refValue_fold R hl _ _ _ hfit, hR2, List.take_left, fold_digits_value]
  unfold readReference
  simp only [h35, beq_self_eq_true, ↓reduceIte, hhex, Bool.false_eq_true]
  rw [hscan]
  have hj : (i + 2 + (Nat.toDigits 10 c.toNat).length == i + 2) = false := by
    rw [hdd]; simp
  have h8 : ¬ (i + 2 + (Nat.toDigits 10 c.toNat).length - (i + 2) > 8) := by omega
  simp only [hj, hsemi, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, h8,
    bind_pure]
  rw [hval, hc]
  simp only [↓reduceIte, Char.ofNat_toNat, refL, List.length_cons, List.length_append, List.length_nil]
  show Except.ok _ = Except.ok _
  congr 2
  omega

/-! ## Names -/

/-- A name the reader reads back: ASCII, a name-start byte first and name
bytes after. -/
@[expose] public def CanonName (s : String) : Prop :=
  (∃ c cs, s.toList = c :: cs ∧ nameStart c.toNat = true) ∧ (∀ d ∈ s.toList, nameByte d.toNat = true) ∧
    ∀ d ∈ s.toList, d.toNat < 128

private theorem nameByte_256 : nameByte 256 = false := by decide

/-- **A name reads back as itself.** -/
private theorem readName_ok (R : List Char) (hl : Ascii R) (bud : Budget) (i : Nat) (name : String)
    (rest : List Char) (hR : R.drop i = name.toList ++ rest) (hn : CanonName name)
    (hb : name.toList.length ≤ bud.name) (hstop : ∀ c ∈ rest.head?, nameByte c.toNat = false) :
    readName bud (bytesOf R) i = .ok (name, i + name.toList.length) := by
  obtain ⟨⟨c, cs, hc, hstart⟩, hbytes, _⟩ := hn
  have hat : at? (bytesOf R) i = c.toNat := by
    apply at?_of_drop R hl i c (cs ++ rest)
    rw [hR, hc]; rfl
  have hscan : scanWhile (bytesOf R) nameByte i = i + name.toList.length := by
    rw [scanWhile_bytesOf R hl _ nameByte_256, hR, runLen_append _ _ _ hbytes hstop]
  unfold readName
  simp only [hat, hstart, ↓reduceIte, hscan, Nat.add_sub_cancel_left]
  have hnb : ¬ (name.toList.length > bud.name) := by omega
  simp only [hnb, ↓reduceIte]
  rw [slice_bytesOf R hl, hR, Nat.add_sub_cancel_left, List.take_left, String.ofList_toList]
  rfl

/-! ## Fallible loops -/

/-- `n` steps of a fallible loop body that ignores its index. -/
private def loopE {ε β : Type} (g : β → Except ε (ForInStep β)) : Nat → β → Except ε β
  | 0, b => .ok b
  | n + 1, b => match g b with
    | .error e => .error e
    | .ok (.done b') => .ok b'
    | .ok (.yield b') => loopE g n b'

private theorem forIn_range'_loopE {ε β : Type} (f : Nat → β → Except ε (ForInStep β))
    (hf : ∀ x b, f x b = f 0 b) (s n : Nat) (b : β) :
    forIn (List.range' s n) b f = loopE (f 0) n b := by
  induction n generalizing s b with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons, hf]
    simp only [loopE]
    cases f 0 b with
    | error e => rfl
    | ok st =>
      cases st with
      | done b' => rfl
      | yield b' => exact ih (s + 1) b'

private theorem forIn_range_loopE {ε β : Type} (f : Nat → β → Except ε (ForInStep β))
    (hf : ∀ x b, f x b = f 0 b) (n : Nat) (b : β) :
    forIn [:n] b f = loopE (f 0) n b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [this]
  exact forIn_range'_loopE f hf _ n b

/-! ## Attribute values -/

private theorem escL_cons (c : Char) (w : List Char) : escL (c :: w) = pieceL c ++ escL w := by
  simp [escL]

private theorem escL_append (a w : List Char) : escL (a ++ w) = escL a ++ escL w := by
  simp [escL, List.flatMap_append]

private theorem literal_toNat (c : Char) (h : literal c = true) :
    32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 38 ∧ c.toNat ≠ 60 ∧ c.toNat ≠ 62 := by
  simp only [literal, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · intro e; exact h3 (Char.ext (UInt32.toNat_inj.mp e))
  · intro e; exact h4 (Char.ext (UInt32.toNat_inj.mp e))
  · intro e; exact h5 (Char.ext (UInt32.toNat_inj.mp e))
  · intro e; exact h6 (Char.ext (UInt32.toNat_inj.mp e))

/-- A character a run of literal value characters holds: literal, not a space. -/
private def runChar (c : Char) : Bool := literal c && c != ' '

private theorem runChar_toNat (c : Char) (h : runChar c = true) :
    33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 38 ∧ c.toNat ≠ 60 ∧ c.toNat ≠ 62 := by
  simp only [runChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  have := literal_toNat c h1
  refine ⟨?_, this.2⟩
  have : c.toNat ≠ 32 := by intro e; exact h2 (Char.ext (UInt32.toNat_inj.mp e))
  omega

private theorem escL_literal (r : List Char) (h : ∀ c ∈ r, literal c = true) : escL r = r := by
  induction r with
  | nil => rfl
  | cons c rest ih =>
    rw [escL_cons, ih (fun d hd => h d (by simp [hd]))]
    simp [pieceL, h c (by simp)]

private theorem utf8ByteSize_ofList_append (u w : List Char) :
    (String.ofList u).utf8ByteSize ≤ (String.ofList (u ++ w)).utf8ByteSize := by
  rw [String.ofList_append, String.utf8ByteSize_append]
  omega

private theorem mem_takeWhile_pred {p : Char → Bool} : ∀ {l : List Char} {x : Char}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · next hy =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact hy
      · exact mem_takeWhile_pred h'
    · simp at h

/-- The value loop over a value's spelling, read through its step's four
behaviours: a run of literal characters is appended, a space is appended,
a reference pushes its character, the closing quote stops. -/
private theorem loopE_value {ε : Type} (g : String × Nat → Except ε (ForInStep (String × Nat)))
    (R rest v : List Char) (limit : Nat) (hlimit : (String.ofList v).utf8ByteSize ≤ limit)
    (hquote : ∀ out j, R.drop j = '"' :: rest → g (out, j) = .ok (.done (out, j)))
    (href : ∀ (out : String) j c tail, R.drop j = refL c ++ tail → xmlChar c.toNat = true →
      (out.push c).utf8ByteSize ≤ limit → g (out, j) = .ok (.yield (out.push c, j + (refL c).length)))
    (hspace : ∀ (out : String) j tail, R.drop j = ' ' :: tail →
      (out ++ String.ofList [' ']).utf8ByteSize ≤ limit →
      g (out, j) = .ok (.yield (out ++ String.ofList [' '], j + 1)))
    (hrun : ∀ (out : String) j r tail, r ≠ [] → (∀ c ∈ r, runChar c = true) → R.drop j = r ++ tail →
      (∀ c ∈ tail.head?, c = '"' ∨ c = ' ' ∨ c = '&') → (out ++ String.ofList r).utf8ByteSize ≤ limit →
      g (out, j) = .ok (.yield (out ++ String.ofList r, j + r.length)))
    (hv : ∀ c ∈ v, xmlChar c.toNat = true) :
    ∀ (n : Nat) (w u : List Char) (j : Nat), u ++ w = v → R.drop j = escL w ++ '"' :: rest →
      w.length < n → loopE g n (String.ofList u, j) = .ok (String.ofList v, j + (escL w).length) := by
  intro n
  induction n with
  | zero => intro w u j _ _ hn; omega
  | succ n ih =>
    intro w u j hu hR hn
    have hpre : ∀ a b, u ++ a ++ b = v → (String.ofList u ++ String.ofList a).utf8ByteSize ≤ limit := by
      intro a b hab
      have := utf8ByteSize_ofList_append (u ++ a) b
      rw [hab] at this
      rw [← String.ofList_append]
      omega
    match w with
    | [] =>
      simp only [List.append_nil] at hu
      subst hu
      simp only [loopE]
      rw [hquote _ j (by simpa [escL] using hR)]
      simp [escL]
    | c :: w' =>
      simp only [loopE]
      by_cases hlit : literal c = true
      · by_cases hsp : c = ' '
        · subst hsp
          have hR' : R.drop j = ' ' :: (escL w' ++ '"' :: rest) := by
            rw [hR, escL_cons]; simp [pieceL, hlit]
          rw [hspace _ j _ hR' (hpre [' '] w' (by simpa using hu))]
          simp only
          rw [← String.ofList_append, ih w' (u ++ [' ']) (j + 1) (by simpa using hu)
            (drop_succ_of R j ' ' _ hR') (by simp at hn; omega)]
          simp [escL_cons, pieceL, hlit]
          omega
        · have hc : runChar c = true := by simp [runChar, hlit, hsp]
          have hsplit := @List.takeWhile_append_dropWhile _ runChar (c :: w')
          generalize hr : (c :: w').takeWhile runChar = r at hsplit
          generalize hw : (c :: w').dropWhile runChar = w'' at hsplit
          have hrc : r = c :: w'.takeWhile runChar := by
            rw [← hr, List.takeWhile_cons]; simp [hc]
          have hrne : r ≠ [] := by rw [hrc]; simp
          have hrun_r : ∀ d ∈ r, runChar d = true := by
            intro d hd
            rw [← hr] at hd
            exact mem_takeWhile_pred hd
          have hlit_r : ∀ d ∈ r, literal d = true := by
            intro d hd
            have := hrun_r d hd
            simp only [runChar, Bool.and_eq_true] at this
            exact this.1
          have hesc : escL (c :: w') = r ++ escL w'' := by
            rw [← hsplit, escL_append, escL_literal r hlit_r]
          have hR' : R.drop j = r ++ (escL w'' ++ '"' :: rest) := by
            rw [hR, hesc, List.append_assoc]
          have hnot := List.head?_dropWhile_not runChar (c :: w')
          rw [hw] at hnot
          have htail : ∀ d ∈ (escL w'' ++ '"' :: rest).head?, d = '"' ∨ d = ' ' ∨ d = '&' := by
            cases w'' with
            | nil => intro d hd; simp [escL] at hd; subst hd; simp
            | cons e es =>
              intro d hd
              have hnot' : runChar e = false := by simpa using hnot
              rw [escL_cons] at hd
              by_cases hle : literal e = true
              · have he : e = ' ' := by
                  simp only [runChar, Bool.and_eq_false_iff] at hnot'
                  rcases hnot' with h | h
                  · simp [hle] at h
                  · simpa using h
                subst he
                simp [pieceL, hle] at hd
                subst hd; simp
              · simp [pieceL, hle, refL] at hd
                subst hd; simp
          have hu' : u ++ r ++ w'' = v := by rw [List.append_assoc, hsplit, hu]
          rw [hrun _ j r _ hrne hrun_r hR' htail (hpre r w'' hu')]
          simp only
          have hlen : (c :: w').length = r.length + w''.length := by
            rw [← hsplit, List.length_append]
          have hrpos : 0 < r.length := by
            rw [hrc]; simp
          rw [← String.ofList_append, ih w'' (u ++ r) (j + r.length) hu'
            (drop_append_of R j r _ hR') (by omega)]
          rw [hesc, List.length_append]
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
          omega
      · have hlitf : literal c = false := by simpa using hlit
        have hpc : pieceL c = refL c := by simp [pieceL, hlitf]
        have hcv : xmlChar c.toNat = true := hv c (by rw [← hu]; simp)
        have hpushL : (String.ofList u).push c = String.ofList (u ++ [c]) := by
          rw [← String.toList_inj]; simp
        have hpush : ((String.ofList u).push c).utf8ByteSize ≤ limit := by
          rw [hpushL]
          have := hpre [c] w' (by simpa using hu)
          rw [← String.ofList_append] at this
          exact this
        rw [href (String.ofList u) j c (escL w' ++ '"' :: rest)
          (by rw [hR, escL_cons, hpc, List.append_assoc]) hcv hpush]
        simp only
        have hdrop : R.drop (j + (refL c).length) = escL w' ++ '"' :: rest :=
          drop_append_of R j (refL c) _ (by rw [hR, escL_cons, hpc, List.append_assoc])
        rw [hpushL, ih w' (u ++ [c]) (j + (refL c).length) (by simpa using hu) hdrop
          (by simp at hn; omega)]
        simp [escL_cons, hpc]
        omega

private theorem pieceL_length (c : Char) : 1 ≤ (pieceL c).length := by
  unfold pieceL; split <;> simp [refL]

private theorem escL_length (v : List Char) : v.length ≤ (escL v).length := by
  induction v with
  | nil => simp [escL]
  | cons c w ih =>
    rw [escL_cons, List.length_append, List.length_cons]
    have := pieceL_length c
    omega

/-- **An attribute value reads back as its characters.** -/
private theorem readValue_ok (R : List Char) (hl : Ascii R) (bud : Budget) (i : Nat) (v : List Char)
    (rest : List Char) (hR : R.drop i = '"' :: (escL v ++ '"' :: rest))
    (hv : ∀ c ∈ v, xmlChar c.toNat = true) (hb : (String.ofList v).utf8ByteSize ≤ bud.text) :
    readValue bud (bytesOf R) i = .ok (String.ofList v, i + 2 + (escL v).length) := by
  have hq : at? (bytesOf R) i = 34 := by rw [at?_of_drop R hl i '"' _ hR]; rfl
  have hR1 : R.drop (i + 1) = escL v ++ '"' :: rest := drop_succ_of R i '"' _ hR
  have hfit : i + 1 + (escL v).length < R.length := by
    have := congrArg List.length hR1
    simp only [List.length_drop, List.length_append, List.length_cons] at this
    omega
  have hlen : v.length ≤ (escL v).length := escL_length v
  unfold readValue
  simp only [hq]
  simp only [show ((34 : Nat) == 34 || (34 : Nat) == 39) = true from rfl, ↓reduceIte]
  rw [forIn_range_loopE _ (fun _ _ => rfl)]
  rw [loopE_value (R := R) (rest := rest) (v := v) (limit := bud.text) _ hb ?quote ?ref ?space ?run hv
    ((bytesOf R).size + 1) v [] (i + 1) (by simp) hR1 (by rw [size_bytesOf]; omega)]
  case quote =>
    intro out j hj
    have : at? (bytesOf R) j = 34 := by rw [at?_of_drop R hl j '"' _ hj]; rfl
    simp [this]
    rfl
  case ref =>
    intro out j c tail hj hc hbud
    have h38 : at? (bytesOf R) j = 38 := by rw [at?_of_drop R hl j '&' _ (by rw [hj]; rfl)]; rfl
    simp only [h38, show ((38 : Nat) == 34) = false from rfl, show ((38 : Nat) == 256) = false from rfl,
      show ((38 : Nat) == 60) = false from rfl, show ((38 : Nat) == 38) = true from rfl,
      Bool.false_eq_true, ↓reduceIte]
    rw [readReference_ref R hl j c tail hj hc]
    have hbud' : out.utf8ByteSize + c.utf8Size ≤ bud.text := by
      rw [String.utf8ByteSize_push] at hbud; exact hbud
    have hnb : ¬ ((out.push c).utf8ByteSize > bud.text) := by omega
    simp only [bind, Except.bind, hnb, ↓reduceIte]
    rfl
  case space =>
    intro out j tail hj hbud
    have h32 : at? (bytesOf R) j = 32 := by rw [at?_of_drop R hl j ' ' _ hj]; rfl
    have hscan : scanWhile (bytesOf R)
        (fun d => d != 34 && d != 256 && d != 60 && d != 38 && !isSpace d) j = j := by
      rw [scanWhile_bytesOf R hl _ (by decide), hj]
      simp [runLen, isSpace]
    have hsl : slice (bytesOf R) j (j + 1) = String.ofList [' '] := by
      rw [slice_bytesOf R hl, hj]; simp
    have hnb : ¬ ((out ++ String.ofList [' ']).utf8ByteSize > bud.text) := by omega
    simp only [h32, show ((32 : Nat) == 34) = false from rfl, show ((32 : Nat) == 256) = false from rfl,
      show ((32 : Nat) == 60) = false from rfl, show ((32 : Nat) == 38) = false from rfl,
      show ((32 : Nat) == 13) = false from rfl, show ((32 : Nat) == 9 || (32 : Nat) == 10) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hscan, beq_self_eq_true, hsl, hnb]
    rfl
  case run =>
    intro out j r tail hrne hrun hj htail hbud
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, r = c :: cs := by
      cases r with
      | nil => exact absurd rfl hrne
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hcn := runChar_toNat c (hrun c (by simp))
    have hat : at? (bytesOf R) j = c.toNat := at?_of_drop R hl j c (cs ++ tail) (by rw [hj]; rfl)
    have hscan : scanWhile (bytesOf R)
        (fun d => d != 34 && d != 256 && d != 60 && d != 38 && !isSpace d) j = j + (c :: cs).length := by
      rw [scanWhile_bytesOf R hl _ (by decide), hj, runLen_append]
      · intro d hd
        have := runChar_toNat d (hrun d hd)
        simp only [isSpace, bne_iff_ne, ne_eq, Bool.and_eq_true, Bool.not_eq_true',
          Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        omega
      · intro d hd
        rcases htail d hd with h | h | h <;> subst h <;> decide
    have hne : (j + (c :: cs).length == j) = false := by simp
    have hsl : slice (bytesOf R) j (j + (c :: cs).length) = String.ofList (c :: cs) := by
      rw [slice_bytesOf R hl, hj, Nat.add_sub_cancel_left, List.take_left]
    have hnb : ¬ ((out ++ String.ofList (c :: cs)).utf8ByteSize > bud.text) := by omega
    have h34 : (c.toNat == 34) = false := by simpa using hcn.2.2.1
    have h256 : (c.toNat == 256) = false := by simp; omega
    have h60 : (c.toNat == 60) = false := by simpa using hcn.2.2.2.2.1
    have h38 : (c.toNat == 38) = false := by simpa using hcn.2.2.2.1
    have h13 : (c.toNat == 13) = false := by simp; omega
    have h910 : (c.toNat == 9 || c.toNat == 10) = false := by simp; omega
    simp only [hat, h34, h256, h60, h38, h13, h910, Bool.false_eq_true, ↓reduceIte, hscan, hne, hsl, hnb]
    rfl
  have hend : at? (bytesOf R) (i + 1 + (escL v).length) = 34 := by
    rw [at?_of_drop R hl _ '"' rest (drop_append_of R (i + 1) _ _ hR1)]; rfl
  simp only [bind, Except.bind, hend, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  show Except.ok _ = Except.ok _
  congr 2
  omega

/-! ## White space and tags -/

private theorem skipSpace_stop (R : List Char) (hl : Ascii R) (j : Nat) (c : Char) (rest : List Char)
    (h : R.drop j = c :: rest) (hc : isSpace c.toNat = false) : skipSpace (bytesOf R) j = j := by
  unfold skipSpace
  rw [scanWhile_bytesOf R hl _ (by decide), h]
  simp [runLen, hc]

private theorem skipSpace_one (R : List Char) (hl : Ascii R) (j : Nat) (c : Char) (rest : List Char)
    (h : R.drop j = ' ' :: c :: rest) (hc : isSpace c.toNat = false) :
    skipSpace (bytesOf R) j = j + 1 := by
  unfold skipSpace
  rw [scanWhile_bytesOf R hl _ (by decide), h]
  rw [show ' ' :: c :: rest = [' '] ++ (c :: rest) from rfl, runLen_append isSpace [' '] (c :: rest)
    (by intro x hx; simp at hx; subst hx; decide) (by intro x hx; simp at hx; subst hx; exact hc)]
  rfl

/-- An attribute's spelling's length. -/
private def attrLen (kv : String × String) : Nat := 1 + kv.1.toList.length + 2 + (escL kv.2.toList).length + 1

/-- What the reader asks of an attribute it reads back: a name it reads, a
value of characters XML admits within the text budget. -/
@[expose] public def CanonAttr (bud : Budget) (kv : String × String) : Prop :=
  CanonName kv.1 ∧ kv.1.toList.length ≤ bud.name ∧ (∀ c ∈ kv.2.toList, xmlChar c.toNat = true) ∧
    kv.2.utf8ByteSize ≤ bud.text

private theorem attrsL_cons (kv : String × String) (rest : List (String × String)) :
    attrsL (kv :: rest) = ' ' :: (kv.1.toList ++ ('=' :: '"' :: (escL kv.2.toList ++ ('"' :: attrsL rest)))) := by
  obtain ⟨k, v⟩ := kv; rfl

private theorem attrsL_length_cons (kv : String × String) (rest : List (String × String)) :
    (attrsL (kv :: rest)).length = attrLen kv + (attrsL rest).length := by
  rw [attrsL_cons]; simp [attrLen]; omega

/-- The names an attribute list leaves remembered. -/
private def insertAll (seen : Std.HashSet String) : List (String × String) → Std.HashSet String
  | [] => seen
  | kv :: rest => insertAll (seen.insert kv.1) rest

/-- The attribute loop of a start tag, read through its step's behaviours:
an attribute is pushed and its name remembered, the tag's end stops with
the result. -/
private theorem loopE_attrs {ε α : Type} (bud : Budget)
    (g : Option α × Array (String × String) × Std.HashSet String × Nat →
      Except ε (ForInStep (Option α × Array (String × String) × Std.HashSet String × Nat)))
    (R tail rest : List Char) (result : Array (String × String) → Nat → α)
    (hattr : ∀ (attrs : Array (String × String)) (seen : Std.HashSet String) (j : Nat)
      (kv : String × String) (more : List Char),
      R.drop j = ' ' :: (kv.1.toList ++ ('=' :: '"' :: (escL kv.2.toList ++ ('"' :: more)))) →
      CanonAttr bud kv → seen.contains kv.1 = false →
      g (none, attrs, seen, j) = .ok (.yield (none, attrs.push kv, seen.insert kv.1, j + attrLen kv)))
    (hend : ∀ (attrs : Array (String × String)) (seen : Std.HashSet String) (j : Nat),
      R.drop j = tail ++ rest → g (none, attrs, seen, j) = .ok (.done (some (result attrs j), attrs, seen, j))) :
    ∀ (as done : List (String × String)) (seen : Std.HashSet String) (j n : Nat),
      (∀ kv ∈ as, CanonAttr bud kv) → ((done ++ as).map (·.1)).Nodup →
      (∀ x, seen.contains x = true ↔ x ∈ done.map (·.1)) →
      R.drop j = attrsL as ++ tail ++ rest → as.length < n →
      loopE g n (none, done.toArray, seen, j) =
        .ok (some (result (done ++ as).toArray (j + (attrsL as).length)), (done ++ as).toArray,
          insertAll seen as, j + (attrsL as).length) := by
  intro as
  induction as with
  | nil =>
    intro done seen j n _ _ _ hR hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [loopE]
    rw [hend _ seen j (by simpa [attrsL] using hR)]
    simp [attrsL, insertAll]
  | cons kv as ih =>
    intro done seen j n hok hnd hseen hR hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [loopE]
    have hkv := hok kv (by simp)
    have hnot : seen.contains kv.1 = false := by
      cases h : seen.contains kv.1 with
      | false => rfl
      | true =>
        have hmem := (hseen kv.1).mp h
        simp only [List.map_append, List.map_cons] at hnd
        have := (List.nodup_append.mp hnd).2.2
        exfalso
        exact this kv.1 hmem kv.1 (by simp) rfl
    rw [hattr done.toArray seen j kv (attrsL as ++ tail ++ rest)
      (by rw [hR, attrsL_cons]; simp) hkv hnot]
    simp only
    have hR' : R.drop (j + attrLen kv) = attrsL as ++ tail ++ rest := by
      have := drop_append_of R j (' ' :: (kv.1.toList ++ ('=' :: '"' :: (escL kv.2.toList ++ ['"']))))
        (attrsL as ++ tail ++ rest) (by rw [hR, attrsL_cons]; simp)
      rw [← this]; congr 1; simp [attrLen]; omega
    have h := ih (done ++ [kv]) (seen.insert kv.1) (j + attrLen kv) n'
      (fun x hx => hok x (by simp [hx])) (by simpa using hnd)
      (fun x => by
        rw [Std.HashSet.contains_insert]
        simp only [Bool.or_eq_true, beq_iff_eq, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton]
        rw [hseen x]
        constructor
        · rintro (h | h)
          · exact Or.inr h.symm
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl h.symm)
      hR' (by simp only [List.length_cons] at hn; omega)
    have harr : done.toArray.push kv = (done ++ [kv]).toArray := by simp
    rw [harr, h]
    simp only [List.append_assoc, List.singleton_append, attrsL_length_cons, Nat.add_assoc, insertAll]

/-- A start tag's closing: `/>` for an empty element, `>` for one with content. -/
private def tagEnd (empty : Bool) : List Char := if empty then ['/', '>'] else ['>']

private theorem nameStart_not (c : Char) (h : nameStart c.toNat = true) :
    isSpace c.toNat = false ∧ c.toNat ≠ 62 ∧ c.toNat ≠ 47 := by
  simp only [nameStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [isSpace, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

/-- **A start tag reads back as its name and attributes.** -/
private theorem readStartTag_ok (R : List Char) (hl : Ascii R) (bud : Budget) (i : Nat) (name : String)
    (attrs : List (String × String)) (empty : Bool) (rest : List Char)
    (hR : R.drop i = '<' :: (name.toList ++ (attrsL attrs ++ (tagEnd empty ++ rest))))
    (hn : CanonName name) (hnb : name.toList.length ≤ bud.name)
    (hattrs : ∀ kv ∈ attrs, CanonAttr bud kv) (hnd : (attrs.map (·.1)).Nodup) :
    readStartTag bud (bytesOf R) i =
      .ok (name, attrs.toArray, empty,
        i + 1 + name.toList.length + (attrsL attrs).length + (tagEnd empty).length) := by
  have hR1 : R.drop (i + 1) = name.toList ++ (attrsL attrs ++ (tagEnd empty ++ rest)) :=
    drop_succ_of R i '<' _ hR
  have hstop : ∀ c ∈ (attrsL attrs ++ (tagEnd empty ++ rest)).head?, nameByte c.toNat = false := by
    intro c hc
    cases attrs with
    | cons kv more =>
      rw [attrsL_cons] at hc
      simp at hc; subst hc; decide
    | nil =>
      cases empty <;> simp [attrsL, tagEnd] at hc <;> subst hc <;> decide
  have hname := readName_ok R hl bud (i + 1) name _ hR1 hn hnb hstop
  have hj0 : R.drop (i + 1 + name.toList.length) = attrsL attrs ++ (tagEnd empty ++ rest) :=
    drop_append_of R (i + 1) _ _ hR1
  unfold readStartTag
  simp only [hname, bind, Except.bind]
  have hlenA : attrs.length ≤ (attrsL attrs).length := by
    clear hattrs hnd hstop hname hj0 hR1 hR
    induction attrs with
    | nil => simp [attrsL]
    | cons kv more ih => rw [attrsL_length_cons]; simp [attrLen]; omega
  have hfit : attrs.length < (bytesOf R).size + 1 := by
    have := congrArg List.length hj0
    simp only [List.length_drop, List.length_append] at this
    rw [size_bytesOf]; omega
  rw [forIn_range_loopE _ (fun _ _ => rfl)]
  rw [loopE_attrs bud _ R (tagEnd empty) rest
    (fun as k => (name, as, empty, k + (tagEnd empty).length)) ?attr ?fin attrs [] ∅
    (i + 1 + name.toList.length) ((bytesOf R).size + 1) hattrs (by simpa using hnd)
    (fun x => by simp [Std.HashSet.contains_empty]) (by rw [hj0, List.append_assoc]) hfit]
  case attr =>
    intro as seen j kv more hj hok hnot
    obtain ⟨⟨c, cs, hc, hstart⟩, hbytes, _⟩ := hok.1
    have hk : skipSpace (bytesOf R) j = j + 1 := by
      apply skipSpace_one R hl j c (cs ++ ('=' :: '"' :: (escL kv.2.toList ++ ('"' :: more))))
      · rw [hj, hc]; rfl
      · exact (nameStart_not c hstart).1
    have hck : at? (bytesOf R) (j + 1) = c.toNat := by
      apply at?_of_drop R hl (j + 1) c (cs ++ ('=' :: '"' :: (escL kv.2.toList ++ ('"' :: more))))
      rw [drop_succ_of R j ' ' _ hj, hc]; rfl
    obtain ⟨h1, h2, h3⟩ := nameStart_not c hstart
    have hjk : R.drop (j + 1) = kv.1.toList ++ ('=' :: '"' :: (escL kv.2.toList ++ ('"' :: more))) :=
      drop_succ_of R j ' ' _ hj
    have han := readName_ok R hl bud (j + 1) kv.1 _ hjk hok.1 hok.2.1 (by intro x hx; simp at hx; subst hx; decide)
    have hk1 : R.drop (j + 1 + kv.1.toList.length) = '=' :: '"' :: (escL kv.2.toList ++ ('"' :: more)) :=
      drop_append_of R (j + 1) _ _ hjk
    have hk2 : skipSpace (bytesOf R) (j + 1 + kv.1.toList.length) = j + 1 + kv.1.toList.length :=
      skipSpace_stop R hl _ '=' _ hk1 (by decide)
    have heq : at? (bytesOf R) (j + 1 + kv.1.toList.length) = 61 := by
      rw [at?_of_drop R hl _ '=' _ hk1]; rfl
    have hk3 : R.drop (j + 1 + kv.1.toList.length + 1) = '"' :: (escL kv.2.toList ++ ('"' :: more)) :=
      drop_succ_of R _ '=' _ hk1
    have hs3 : skipSpace (bytesOf R) (j + 1 + kv.1.toList.length + 1) = j + 1 + kv.1.toList.length + 1 :=
      skipSpace_stop R hl _ '"' _ hk3 (by decide)
    have hv := readValue_ok R hl bud _ kv.2.toList more hk3 hok.2.2.1 (by
      rw [String.ofList_toList]; exact hok.2.2.2)
    rw [String.ofList_toList] at hv
    simp only [hk, hck]
    have hne62 : (c.toNat == 62) = false := by simpa using h2
    have hne47 : (c.toNat == 47) = false := by simpa using h3
    have hjne : (j + 1 == j) = false := by simp
    simp only [hne62, hne47, hjne, Bool.false_eq_true, ↓reduceIte, han, hk2, heq,
      bne_self_eq_false, hs3, hv, hnot]
    show Except.ok _ = Except.ok _
    congr 3
    simp [attrLen]; omega
  case fin =>
    intro as seen j hj
    cases empty with
    | false =>
      have h62 : at? (bytesOf R) j = 62 := by
        rw [at?_of_drop R hl j '>' rest (by simpa [tagEnd] using hj)]; rfl
      have hk : skipSpace (bytesOf R) j = j := skipSpace_stop R hl j '>' rest (by simpa [tagEnd] using hj) (by decide)
      simp only [hk, h62, beq_self_eq_true, ↓reduceIte]
      rfl
    | true =>
      have hj' : R.drop j = '/' :: '>' :: rest := by simpa [tagEnd] using hj
      have h47 : at? (bytesOf R) j = 47 := by rw [at?_of_drop R hl j '/' _ hj']; rfl
      have h62 : at? (bytesOf R) (j + 1) = 62 := by
        rw [at?_of_drop R hl (j + 1) '>' rest (drop_succ_of R j '/' _ hj')]; rfl
      have hk : skipSpace (bytesOf R) j = j := skipSpace_stop R hl j '/' _ hj' (by decide)
      simp only [hk, h47, h62, show ((47 : Nat) == 62) = false from rfl, Bool.false_eq_true,
        beq_self_eq_true, ↓reduceIte]
      rfl
  simp only [List.nil_append]
  rfl

/-! ## The reader's steps over the spelling -/

/-- A state with `k` more nodes counted. -/
private def bump (s : State) (k : Nat) : State := { s with nodes := s.nodes + k }

private theorem tick_ok (bud : Budget) (s : State) (h : s.nodes + 1 ≤ bud.nodes) :
    s.tick bud = .ok (bump s 1) := by
  unfold State.tick
  have : ¬ (s.nodes + 1 > bud.nodes) := by omega
  simp only [this, ↓reduceIte]
  rfl

/-- **A start tag is one step**: an empty element given to its parent, or an
element opened, one more node counted. -/
private theorem step_start (R : List Char) (hl : Ascii R) (bud : Budget) (s : State) (name : String)
    (attrs : List (String × String)) (empty : Bool) (rest : List Char)
    (hR : R.drop s.pos = '<' :: (name.toList ++ (attrsL attrs ++ (tagEnd empty ++ rest))))
    (hn : CanonName name) (hnb : name.toList.length ≤ bud.name)
    (hattrs : ∀ kv ∈ attrs, CanonAttr bud kv) (hnd : (attrs.map (·.1)).Nodup)
    (hroot : ¬ (s.stack.isEmpty = true ∧ s.root.isSome = true))
    (hnodes : s.nodes + 1 ≤ bud.nodes) (hdepth : s.stack.size + 1 ≤ bud.depth) :
    step bud (bytesOf R) s = .ok (
      let j := s.pos + 1 + name.toList.length + (attrsL attrs).length + (tagEnd empty).length
      if empty then ((bump s 1).give (.elem name attrs.toArray #[])).at j
      else (bump s 1).openAt { name, attrs := attrs.toArray, kids := #[], text := "" } j) := by
  obtain ⟨⟨c, cs, hc, hstart⟩, _, _⟩ := hn
  have h60 : at? (bytesOf R) s.pos = 60 := by rw [at?_of_drop R hl s.pos '<' _ hR]; rfl
  have hR1 := drop_succ_of R s.pos '<' _ hR
  have hd : at? (bytesOf R) (s.pos + 1) = c.toNat := by
    apply at?_of_drop R hl (s.pos + 1) c (cs ++ (attrsL attrs ++ (tagEnd empty ++ rest)))
    rw [hR1, hc]; rfl
  have hcn : c.toNat ≠ 47 ∧ c.toNat ≠ 33 ∧ c.toNat ≠ 63 := by
    simp only [nameStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hstart
    omega
  have htag := readStartTag_ok R hl bud s.pos name attrs empty rest hR ⟨⟨c, cs, hc, hstart⟩, ‹_›, ‹_›⟩ hnb hattrs hnd
  unfold step startTag
  simp only [h60, hd, show ((60 : Nat) == 60) = true from rfl, ↓reduceIte]
  have h47 : (c.toNat == 47) = false := by simpa using hcn.1
  have h33 : (c.toNat == 33) = false := by simpa using hcn.2.1
  have h63 : (c.toNat == 63) = false := by simpa using hcn.2.2
  simp only [h47, h33, h63, Bool.false_eq_true, ↓reduceIte]
  have hr : (s.stack.isEmpty && s.root.isSome) = false := by
    cases h1 : s.stack.isEmpty <;> cases h2 : s.root.isSome <;> simp_all
  simp only [hr, Bool.false_eq_true, ↓reduceIte, tick_ok bud s hnodes, htag]
  have hd' : ¬ ((bump s 1).stack.size + 1 > bud.depth) := by simp [bump]; omega
  simp only [hd', ↓reduceIte]
  cases empty <;> rfl

/-- **An end tag is one step**: the open element closed onto its parent. -/
private theorem step_end (R : List Char) (hl : Ascii R) (bud : Budget) (s : State) (name : String)
    (rest : List Char) (f : Frame)
    (hR : R.drop s.pos = '<' :: '/' :: (name.toList ++ ('>' :: rest)))
    (hn : CanonName name) (hnb : name.toList.length ≤ bud.name)
    (hf : s.stack.back? = some f) (hname : f.name = name) :
    step bud (bytesOf R) s = .ok (s.closeAt f (s.pos + 2 + name.toList.length + 1)) := by
  have h60 : at? (bytesOf R) s.pos = 60 := by rw [at?_of_drop R hl s.pos '<' _ hR]; rfl
  have hR1 := drop_succ_of R s.pos '<' _ hR
  have h47 : at? (bytesOf R) (s.pos + 1) = 47 := by rw [at?_of_drop R hl _ '/' _ hR1]; rfl
  have hR2 : R.drop (s.pos + 2) = name.toList ++ ('>' :: rest) := by
    have := drop_succ_of R (s.pos + 1) '/' _ hR1
    simpa using this
  have hrn := readName_ok R hl bud (s.pos + 2) name ('>' :: rest) hR2 hn hnb
    (by intro x hx; simp at hx; subst hx; decide)
  have hR3 : R.drop (s.pos + 2 + name.toList.length) = '>' :: rest := drop_append_of R _ _ _ hR2
  have hk : skipSpace (bytesOf R) (s.pos + 2 + name.toList.length) = s.pos + 2 + name.toList.length :=
    skipSpace_stop R hl _ '>' rest hR3 (by decide)
  have h62 : at? (bytesOf R) (s.pos + 2 + name.toList.length) = 62 := by
    rw [at?_of_drop R hl _ '>' rest hR3]; rfl
  unfold step endTag
  simp only [h60, h47, show ((60 : Nat) == 60) = true from rfl, show ((47 : Nat) == 47) = true from rfl,
    ↓reduceIte, hrn, hk, h62, hf, hname, show ((62 : Nat) != 62) = false from rfl, Bool.false_eq_true,
    bne_self_eq_false]

/-- **A reference is one step**: its character appended to the open
element's text, within the text budget, one more node counted. -/
private theorem step_ref (R : List Char) (hl : Ascii R) (bud : Budget) (s : State) (c : Char)
    (rest : List Char) (hR : R.drop s.pos = refL c ++ rest) (hc : xmlChar c.toNat = true)
    (hopen : s.stack.isEmpty = false) (f : Frame) (hf : s.stack.back? = some f)
    (htext : f.text.utf8ByteSize + c.utf8Size ≤ bud.text) (hnodes : s.nodes + 1 ≤ bud.nodes) :
    step bud (bytesOf R) s = .ok ((bump (s.chars (String.singleton c)) 1).at (s.pos + (refL c).length)) := by
  have h38 : at? (bytesOf R) s.pos = 38 := by
    rw [at?_of_drop R hl s.pos '&' _ (by rw [hR]; rfl)]; rfl
  have hchars : (s.chars (String.singleton c)).nodes = s.nodes := by
    unfold State.chars; split <;> rfl
  have hnb : ¬ ((s.stack.back?.map fun x => x.text.utf8ByteSize + c.utf8Size).getD 0 > bud.text) := by
    rw [hf]; simp only [Option.map_some, Option.getD_some]; omega
  unfold step reference
  simp only [h38, show ((38 : Nat) == 60) = false from rfl, show ((38 : Nat) == 38) = true from rfl,
    Bool.false_eq_true, ↓reduceIte, hopen, readReference_ref R hl s.pos c rest hR hc, hnb]
  rw [tick_ok bud _ (by rw [hchars]; exact hnodes)]
  rfl

/-! ## Matching a spelling -/

private theorem forIn_match_true (b t : ByteArray) (i : Nat) : ∀ (l : List Nat) (ok : Bool),
    (forIn l ok (fun k (ok : Bool) => (if (at? b (i + k) != at? t k) = true then pure (ForInStep.done false)
      else pure (ForInStep.yield ok) : Id (ForInStep Bool)))).run = true →
    ok = true ∧ ∀ k ∈ l, at? b (i + k) = at? t k := by
  intro l
  induction l with
  | nil => intro ok h; exact ⟨h, by simp⟩
  | cons k l ih =>
    intro ok h
    rw [List.forIn_cons] at h
    by_cases hk : (at? b (i + k) != at? t k) = true
    · simp [hk] at h
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := ih ok h
      refine ⟨h1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hk
      · exact h2 x hx

/-- **What `bytesAt` reports**: the string's bytes stand at `i`. -/
private theorem bytesAt_spec (b : ByteArray) (i : Nat) (s : String) (h : bytesAt b i s = true) :
    i + s.toUTF8.size ≤ b.size ∧ ∀ k < s.toUTF8.size, at? b (i + k) = at? s.toUTF8 k := by
  unfold bytesAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h2
  have := (forIn_match_true b s.toUTF8 i _ true h2).2
  intro k hk
  apply this
  simp only [Std.Legacy.Range.size, List.mem_range'_1]
  omega

/-- `find`'s loop, ignoring its index. -/
private def findStep (b : ByteArray) (s : String) (first : Nat) (st : Option (Option Nat) × Nat) :
    ForInStep (Option (Option Nat) × Nat) :=
  if st.2 ≥ b.size then .done (some none, st.2)
  else if (at? b st.2 == first && bytesAt b st.2 s) = true then .done (some (some st.2), st.2)
  else .yield (none, st.2 + 1)

private theorem loopN_find (b : ByteArray) (s : String) (first k : Nat) :
    ∀ (n j : Nat), (loopN (findStep b s first) n (none, j)).1 = some (some k) → bytesAt b k s = true := by
  intro n
  induction n with
  | zero => intro j h; simp [loopN] at h
  | succ n ih =>
    intro j h
    simp only [loopN] at h
    by_cases hj : j ≥ b.size
    · simp [findStep, hj] at h
    · by_cases hm : (at? b j == first && bytesAt b j s) = true
      · simp only [findStep, hj, hm, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hm
        exact hm.2
      · simp only [findStep, hj, hm, ↓reduceIte, Bool.false_eq_true] at h
        exact ih (j + 1) h

/-- **What `find` reports**: the string stands where it says. -/
private theorem find_eq (b : ByteArray) (i : Nat) (s : String) :
    find b i s = (match (loopN (findStep b s (at? s.toUTF8 0)) (b.size + 1) (none, i)).1 with
      | some r => r
      | none => none) := by
  unfold find
  simp only [Id.run_bind]
  rw [forIn_range_loopN (findStep b s (at? s.toUTF8 0)) _ (fun _ st => by
    simp only [findStep]; split <;> (try split) <;> rfl)]
  generalize (loopN (findStep b s (at? s.toUTF8 0)) (b.size + 1) (none, i)) = st
  obtain ⟨r, j⟩ := st
  cases r <;> rfl

private theorem find_some (b : ByteArray) (i : Nat) (s : String) (k : Nat) (h : find b i s = some k) :
    bytesAt b k s = true := by
  rw [find_eq] at h
  apply loopN_find b s (at? s.toUTF8 0) k (b.size + 1) i
  generalize (loopN (findStep b s (at? s.toUTF8 0)) (b.size + 1) (none, i)) = st at h
  obtain ⟨r, j⟩ := st
  cases r with
  | none => simp at h
  | some r => simp only at h; simp [h]

private theorem toList_ascii3 : "]]>".toList = [']', ']', '>'] := by decide

private theorem ascii3 : Ascii [']', ']', '>'] := by
  intro c hc; simp at hc; rcases hc with rfl | rfl | rfl <;> decide

private theorem cdataEnd_toUTF8 : "]]>".toUTF8 = bytesOf [']', ']', '>'] := by
  rw [toUTF8_ascii _ (by rw [toList_ascii3]; exact ascii3), toList_ascii3]

/-- **No `]]>` stands in a run of literal characters**, which holds no `>`. -/
private theorem find_cdataEnd_none (r : List Char) (hlit : ∀ c ∈ r, literal c = true) :
    find (bytesOf r) 0 "]]>" = none := by
  have hasc : Ascii r := fun c hc => by have := literal_toNat c (hlit c hc); omega
  cases h : find (bytesOf r) 0 "]]>" with
  | none => rfl
  | some k =>
    have hb := bytesAt_spec _ _ _ (find_some _ _ _ _ h)
    rw [cdataEnd_toUTF8, size_bytesOf] at hb
    have h2 := hb.2 2 (by simp)
    have h62 : at? (bytesOf [']', ']', '>']) 2 = 62 := by rw [at?_bytesOf _ _ ascii3]; rfl
    rw [h62, at?_bytesOf _ _ hasc] at h2
    have hk : k + 2 < r.length := by simp [size_bytesOf] at hb; omega
    rw [List.getElem?_eq_getElem hk] at h2
    have := literal_toNat _ (hlit _ (List.getElem_mem hk))
    simp at h2
    omega

private theorem contains_bytesOf (r : List Char) (n : UInt8) (hn : ∀ c ∈ r, UInt8.ofNat c.toNat ≠ n) :
    (bytesOf r).data.contains n = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [Array.contains_iff_mem] at h
  simp only [bytesOf, List.data_toByteArray, List.mem_toArray, List.mem_map] at h
  obtain ⟨c, hc, he⟩ := h
  exact hn c hc he

/-- **A run of literal characters reads as itself**: no line end to
normalize. -/
private theorem normalizeEol_literal (r : List Char) (hlit : ∀ c ∈ r, literal c = true) :
    normalizeEol (bytesOf r) = String.ofList r := by
  have hasc : Ascii r := fun c hc => by have := literal_toNat c (hlit c hc); omega
  unfold normalizeEol
  rw [contains_bytesOf r 13 (fun c hc he => by
    have := literal_toNat c (hlit c hc)
    have h13 := congrArg UInt8.toNat he
    simp only [UInt8.toNat_ofNat'] at h13
    have : (13 : UInt8).toNat = 13 := rfl
    omega)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [fromUTF8?_bytesOf r hasc]
  rfl

/-- **Character data of literal characters reads back as itself.** -/
private theorem readChars_run (R : List Char) (hl : Ascii R) (i : Nat) (r tail : List Char)
    (hlit : ∀ c ∈ r, literal c = true) (hR : R.drop i = r ++ tail)
    (htail : ∀ c ∈ tail.head?, c = '&' ∨ c = '<') :
    readChars (bytesOf R) i = .ok (String.ofList r, i + r.length) := by
  have hscan : scanWhile (bytesOf R) (fun c => c != 60 && c != 38 && c != 256) i = i + r.length := by
    rw [scanWhile_bytesOf R hl _ (by decide), hR, runLen_append]
    · intro c hc
      have := literal_toNat c (hlit c hc)
      simp only [bne_iff_ne, ne_eq, Bool.and_eq_true]
      omega
    · intro c hc
      rcases htail c hc with h | h <;> subst h <;> decide
  have hraw : (bytesOf R).extract i (i + r.length) = bytesOf r := by
    rw [extract_bytesOf, hR, Nat.add_sub_cancel_left, List.take_left]
  unfold readChars
  simp only [hscan, hraw, find_cdataEnd_none r hlit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    normalizeEol_literal r hlit]
  rfl

private theorem isEmpty_of_back (a : Array Frame) (f : Frame) (h : a.back? = some f) : a.isEmpty = false := by
  cases he : a.isEmpty with
  | false => rfl
  | true =>
    rw [Array.isEmpty_iff] at he
    subst he
    simp at h

/-- **A run of literal characters is one step**: appended to the open
element's text, one more node counted. -/
private theorem step_chars (R : List Char) (hl : Ascii R) (bud : Budget) (s : State) (r tail : List Char)
    (hr : r ≠ []) (hlit : ∀ c ∈ r, literal c = true) (hR : R.drop s.pos = r ++ tail)
    (htail : ∀ c ∈ tail.head?, c = '&' ∨ c = '<') (f : Frame) (hf : s.stack.back? = some f)
    (htext : f.text.utf8ByteSize + (String.ofList r).utf8ByteSize ≤ bud.text)
    (hnodes : s.nodes + 1 ≤ bud.nodes) :
    step bud (bytesOf R) s = .ok ((bump (s.chars (String.ofList r)) 1).at (s.pos + r.length)) := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, r = c :: cs := by
    cases r with
    | nil => exact absurd rfl hr
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hcn := literal_toNat c (hlit c (by simp))
  have hat : at? (bytesOf R) s.pos = c.toNat := at?_of_drop R hl s.pos c (cs ++ tail) (by rw [hR]; rfl)
  have h60 : (c.toNat == 60) = false := by simpa using hcn.2.2.2.2.1
  have h38 : (c.toNat == 38) = false := by simpa using hcn.2.2.2.1
  have hchars : (s.chars (String.ofList (c :: cs))).nodes = s.nodes := by
    unfold State.chars; split <;> rfl
  have hempty := isEmpty_of_back _ _ hf
  have hnb : ¬ ((s.stack.back?.map fun x => x.text.utf8ByteSize + (String.ofList (c :: cs)).utf8ByteSize).getD 0
      > bud.text) := by
    rw [hf]; simp only [Option.map_some, Option.getD_some]; omega
  unfold step charData
  simp only [hat, h60, h38, Bool.false_eq_true, ↓reduceIte, readChars_run R hl s.pos (c :: cs) tail hlit hR htail,
    hempty, hnb]
  rw [tick_ok bud _ (by rw [hchars]; exact hnodes)]
  rfl

/-! ## The reader's run -/

/-- `m` steps, each one forward, take the reader from `s` to `t`. -/
private inductive Reach (bud : Budget) (b : ByteArray) : State → State → Nat → Prop
  | refl (s : State) : Reach bud b s s 0
  | cons {s t u : State} {m : Nat} : step bud b s = .ok t → s.pos < t.pos → Reach bud b t u m →
      Reach bud b s u (m + 1)

private theorem Reach.trans {bud : Budget} {b : ByteArray} {s t u : State} {m k : Nat}
    (h1 : Reach bud b s t m) (h2 : Reach bud b t u k) : Reach bud b s u (k + m) := by
  induction h1 with
  | refl => simpa using h2
  | cons hs hp _ ih =>
    rw [← Nat.add_assoc]
    exact Reach.cons hs hp (ih h2)

private theorem Reach.single {bud : Budget} {b : ByteArray} {s t : State} (h : step bud b s = .ok t)
    (hp : s.pos < t.pos) : Reach bud b s t 1 :=
  Reach.cons h hp (Reach.refl t)

private theorem Reach.pos_le {bud : Budget} {b : ByteArray} {s t : State} {m : Nat} (h : Reach bud b s t m) :
    s.pos + m ≤ t.pos := by
  induction h with
  | refl => simp
  | cons _ hp _ ih => omega

private theorem Reach.cast {bud : Budget} {b : ByteArray} {s t t' : State} {m : Nat} (h : Reach bud b s t m)
    (he : t = t') : Reach bud b s t' m := he ▸ h

/-- The run's step, ignoring its index. -/
private def runStep (bud : Budget) (b : ByteArray) (acc : Except Refusal State) : ForInStep (Except Refusal State) :=
  match acc with
  | .error e => .done (.error e)
  | .ok s =>
    if s.pos ≥ b.size then .done (.ok s)
    else match step bud b s with
      | .error e => .done (.error e)
      | .ok s' => if s'.pos ≤ s.pos then .done (.error (.syntax s.pos "no progress")) else .yield (.ok s')

private theorem run_loopN (bud : Budget) (b : ByteArray) (start : Nat) :
    run bud b start = loopN (runStep bud b) (b.size + 1)
      (.ok { pos := start, stack := #[], root := none, nodes := 0, doctype := false }) := by
  unfold run
  exact forIn_range_loopN (runStep bud b) _ (fun _ _ => rfl) _ _

private theorem loopN_reach {bud : Budget} {b : ByteArray} {s t : State} {m : Nat} (h : Reach bud b s t m)
    (ht : t.pos ≤ b.size) :
    ∀ k, loopN (runStep bud b) (k + m) (.ok s) = loopN (runStep bud b) k (.ok t) := by
  induction h with
  | refl => intro k; rfl
  | @cons s₀ t₀ u₀ m₀ hs hp r ih =>
    intro k
    have hle := r.pos_le
    rw [show k + (m₀ + 1) = (k + m₀) + 1 by omega]
    simp only [loopN, runStep]
    have h1 : ¬ (s₀.pos ≥ b.size) := by omega
    have h2 : ¬ (t₀.pos ≤ s₀.pos) := by omega
    simp only [h1, ↓reduceIte, hs, h2]
    exact ih ht k

/-- **A run of forward steps to the end is the reader's run.** -/
private theorem run_reach {bud : Budget} {b : ByteArray} {start : Nat} {u : State} {m : Nat}
    (h : Reach bud b { pos := start, stack := #[], root := none, nodes := 0, doctype := false } u m)
    (hu : u.pos = b.size) : run bud b start = .ok u := by
  rw [run_loopN]
  have hle := h.pos_le
  simp only at hle
  rw [show b.size + 1 = (b.size - m + 1) + m by omega, loopN_reach h (by omega)]
  simp only [loopN, runStep, hu, ge_iff_le, Nat.le_refl, ↓reduceIte]

/-! ## States -/

private theorem chars_push (s : State) (stk : Array Frame) (f : Frame) (h : s.stack = stk.push f) (t : String) :
    s.chars t = { s with stack := stk.push { f with text := f.text ++ t } } := by
  unfold State.chars
  rw [h, Array.back?_push]
  simp only [Array.pop_push]

private theorem give_push (s : State) (stk : Array Frame) (f : Frame) (h : s.stack = stk.push f) (n : Node) :
    s.give n = { s with stack := stk.push { f.flush with kids := f.flush.kids.push n } } := by
  unfold State.give
  rw [h, Array.back?_push]
  simp only [Array.pop_push]

private theorem give_root (s : State) (h : s.stack = #[]) (n : Node) : s.give n = { s with root := some n } := by
  unfold State.give
  rw [h]
  rfl

private theorem give_bump (s : State) (k : Nat) (n : Node) : (bump s k).give n = bump (s.give n) k := by
  obtain ⟨pos, stack, root, nodes, doctype⟩ := s
  simp only [State.give, bump]
  split <;> rfl

/-! ## Text -/

/-- **A text's spelling reads back as its characters**, appended to the
open element's text: a run of literal characters a step, a reference a
step. -/
private theorem text_reads (R : List Char) (hl : Ascii R) (bud : Budget) :
    ∀ (n : Nat) (l : List Char) (s : State) (stk : Array Frame) (f : Frame) (rest : List Char),
    l.length < n → s.stack = stk.push f → R.drop s.pos = escL l ++ rest →
    (∀ c ∈ rest.head?, c = '<') → (∀ c ∈ l, xmlChar c.toNat = true) →
    (f.text ++ String.ofList l).utf8ByteSize ≤ bud.text → s.nodes + l.length ≤ bud.nodes →
    ∃ k m, k ≤ l.length ∧ Reach bud (bytesOf R) s
      { s with stack := stk.push { f with text := f.text ++ String.ofList l }, nodes := s.nodes + k,
               pos := s.pos + (escL l).length } m := by
  intro n
  induction n with
  | zero => intro l s stk f rest hn; omega
  | succ n ih =>
    intro l s stk f rest hn hs hR hnext hx htext hnodes
    match l with
    | [] =>
      refine ⟨0, 0, Nat.le_refl _, ?_⟩
      apply (Reach.refl s).cast
      obtain ⟨pos, stack, root, nodes, doctype⟩ := s
      simp only at hs
      subst hs
      simp [escL]
    | c :: l' =>
      have hstack : s.stack.isEmpty = false := by rw [hs]; simp
      by_cases hlit : literal c = true
      · have hsplit := @List.takeWhile_append_dropWhile _ literal (c :: l')
        generalize hr : (c :: l').takeWhile literal = r at hsplit
        generalize hw : (c :: l').dropWhile literal = w at hsplit
        have hrc : r = c :: l'.takeWhile literal := by
          rw [← hr, List.takeWhile_cons]; simp [hlit]
        have hrne : r ≠ [] := by rw [hrc]; simp
        have hlit_r : ∀ d ∈ r, literal d = true := by
          intro d hd
          rw [← hr] at hd
          exact mem_takeWhile_pred hd
        have hesc : escL (c :: l') = r ++ escL w := by
          rw [← hsplit, escL_append, escL_literal r hlit_r]
        have hR' : R.drop s.pos = r ++ (escL w ++ rest) := by
          rw [hR, hesc, List.append_assoc]
        have hnot := List.head?_dropWhile_not literal (c :: l')
        rw [hw] at hnot
        have htail : ∀ d ∈ (escL w ++ rest).head?, d = '&' ∨ d = '<' := by
          cases w with
          | nil => intro d hd; simp [escL] at hd; exact Or.inr (hnext d hd)
          | cons e es =>
            intro d hd
            have hnot' : literal e = false := by simpa using hnot
            rw [escL_cons] at hd
            simp [pieceL, hnot', refL] at hd
            subst hd; simp
        have hlen : (c :: l').length = r.length + w.length := by
          rw [← hsplit, List.length_append]
        have hrpos : 0 < r.length := by rw [hrc]; simp
        have hofl : String.ofList (c :: l') = String.ofList r ++ String.ofList w := by
          rw [← String.ofList_append, hsplit]
        have hbud : f.text.utf8ByteSize + (String.ofList r).utf8ByteSize ≤ bud.text := by
          rw [hofl, ← String.append_assoc, String.utf8ByteSize_append, String.utf8ByteSize_append] at htext
          omega
        have hf : s.stack.back? = some f := by rw [hs, Array.back?_push]
        have hstep := step_chars R hl bud s r (escL w ++ rest) hrne hlit_r hR' htail f hf hbud (by omega)
        let s₁ := (bump (s.chars (String.ofList r)) 1).at (s.pos + r.length)
        let f₁ : Frame := { f with text := f.text ++ String.ofList r }
        have hs₁ : s₁.stack = stk.push f₁ := by
          simp only [s₁, f₁, State.at, bump, chars_push s stk f hs]
        have hR₁ : R.drop s₁.pos = escL w ++ rest := drop_append_of R s.pos r _ hR'
        have hx₁ : ∀ d ∈ w, xmlChar d.toNat = true := by
          intro d hd; apply hx d; rw [← hsplit]; simp [hd]
        have htext₁ : (f₁.text ++ String.ofList w).utf8ByteSize ≤ bud.text := by
          simp only [f₁]; rw [String.append_assoc, ← hofl]; exact htext
        have hnodes₁ : s₁.nodes + w.length ≤ bud.nodes := by
          simp only [s₁, State.at, bump, chars_push s stk f hs]; omega
        obtain ⟨k, m, hk, hreach⟩ := ih w s₁ stk f₁ rest (by omega) hs₁ hR₁ hnext hx₁ htext₁ hnodes₁
        refine ⟨k + 1, m + 1, by omega, ?_⟩
        apply (Reach.cons hstep (by simp [State.at]; omega) hreach).cast
        simp only [s₁, f₁, State.at, bump, chars_push s stk f hs, hesc, List.length_append,
          String.append_assoc, ← hofl]
        congr 1 <;> omega
      · have hlitf : literal c = false := by simpa using hlit
        have hpc : pieceL c = refL c := by simp [pieceL, hlitf]
        have hcx : xmlChar c.toNat = true := hx c (by simp)
        have hR' : R.drop s.pos = refL c ++ (escL l' ++ rest) := by
          rw [hR, escL_cons, hpc, List.append_assoc]
        have hofl : String.ofList (c :: l') = String.singleton c ++ String.ofList l' := by
          rw [← String.toList_inj]; simp
        have hbud : f.text.utf8ByteSize + c.utf8Size ≤ bud.text := by
          rw [hofl, String.utf8ByteSize_append, String.utf8ByteSize_append] at htext
          have := String.utf8ByteSize_singleton (c := c)
          omega
        have hstep := step_ref R hl bud s c (escL l' ++ rest) hR' hcx hstack f (by rw [hs, Array.back?_push])
          hbud (by simp at hnodes; omega)
        let s₁ := (bump (s.chars (String.singleton c)) 1).at (s.pos + (refL c).length)
        let f₁ : Frame := { f with text := f.text ++ String.singleton c }
        have hs₁ : s₁.stack = stk.push f₁ := by
          simp only [s₁, f₁, State.at, bump, chars_push s stk f hs]
        have hR₁ : R.drop s₁.pos = escL l' ++ rest := drop_append_of R s.pos (refL c) _ hR'
        have htext₁ : (f₁.text ++ String.ofList l').utf8ByteSize ≤ bud.text := by
          simp only [f₁]; rw [String.append_assoc, ← hofl]; exact htext
        have hnodes₁ : s₁.nodes + l'.length ≤ bud.nodes := by
          simp only [s₁, State.at, bump, chars_push s stk f hs]; simp at hnodes; omega
        obtain ⟨k, m, hk, hreach⟩ := ih l' s₁ stk f₁ rest (by simp at hn; omega) hs₁ hR₁ hnext
          (fun d hd => hx d (by simp [hd])) htext₁ hnodes₁
        refine ⟨k + 1, m + 1, by simp; omega, ?_⟩
        have hpos : 0 < (refL c).length := by simp [refL]
        apply (Reach.cons hstep (by simp [State.at]; omega) hreach).cast
        simp only [s₁, f₁, State.at, bump, chars_push s stk f hs, escL_cons, hpc, List.length_append,
          String.append_assoc, ← hofl]
        congr 1 <;> omega

/-! ## Trees -/

/-- A node handed to the reader's state as its spelling hands it: text to
the open element's text, an element to the open element or the root. -/
private def State.take (s : State) : Node → State
  | .text t => s.chars t
  | .elem name attrs kids => s.give (.elem name attrs kids)

/-- The open element once a node is handed to it. -/
private def Frame.takes (f : Frame) : Node → Frame
  | .text t => { f with text := f.text ++ t }
  | .elem name attrs kids => { f.flush with kids := f.flush.kids.push (.elem name attrs kids) }

/-- Is the node text? -/
@[expose] public def Node.isText : Node → Bool
  | .text _ => true
  | .elem .. => false

/-- Does the list open with text? -/
@[expose] public def startsText : List Node → Bool
  | n :: _ => n.isText
  | [] => false

mutual

-- conserves: none — a bound on the reader's count over a tree's spelling, which the budget bounds.
/-- At most the nodes the reader counts reading a tree's spelling: an element
one, a text one per character at most. -/
@[expose] public def Node.ticks : Node → Nat
  | .elem _ _ kids => Node.ticksList kids.toList + 1
  | .text t => t.length
@[expose] public def Node.ticksList : List Node → Nat
  | [] => 0
  | n :: rest => Node.ticks n + Node.ticksList rest
end

mutual

-- conserves: none — a condition on a tree, not a walk over it.
/-- What the reader asks of a tree it reads back as it stands: names it
reads, each attribute named once, characters XML admits within the text
budget, no text empty and no two texts adjacent. -/
@[expose] public def CanonNode (bud : Budget) : Node → Prop
  | .elem name attrs kids => CanonName name ∧ name.toList.length ≤ bud.name ∧
      (∀ kv ∈ attrs.toList, CanonAttr bud kv) ∧ (attrs.toList.map (·.1)).Nodup ∧ CanonKids bud kids.toList
  | .text t => t ≠ "" ∧ (∀ c ∈ t.toList, xmlChar c.toNat = true) ∧ t.utf8ByteSize ≤ bud.text
@[expose] public def CanonKids (bud : Budget) : List Node → Prop
  | [] => True
  | n :: rest => CanonNode bud n ∧ CanonKids bud rest ∧ (n.isText = true → startsText rest = false)
end

private theorem take_push (s : State) (stk : Array Frame) (f : Frame) (h : s.stack = stk.push f) (n : Node) :
    s.take n = { s with stack := stk.push (f.takes n) } := by
  cases n with
  | text t => simp only [State.take, Frame.takes, chars_push s stk f h]
  | elem name attrs kids => simp only [State.take, Frame.takes, give_push s stk f h]

private theorem flush_text (f : Frame) : f.flush.text = "" := by
  unfold Frame.flush; split
  · next h => simpa using h
  · rfl

private theorem flush_name (f : Frame) : f.flush.name = f.name := by
  unfold Frame.flush; split <;> rfl

private theorem flush_attrs (f : Frame) : f.flush.attrs = f.attrs := by
  unfold Frame.flush; split <;> rfl

private theorem flush_clean (f : Frame) (h : f.text = "") : f.flush = f := by
  unfold Frame.flush; simp [h]

private theorem takes_flush (f : Frame) (n : Node) (hclean : n.isText = true → f.text = "")
    (hne : ∀ t, n = .text t → t ≠ "") : (f.takes n).flush.kids = f.flush.kids.push n := by
  cases n with
  | text t =>
    have h0 := hclean rfl
    have ht := hne t rfl
    simp only [Frame.takes, h0, String.empty_append, flush_clean f h0]
    unfold Frame.flush
    simp [ht]
  | elem name attrs kids =>
    simp only [Frame.takes]
    rw [flush_clean _ (by simp [flush_text])]

private theorem takes_clean (f : Frame) (n : Node) (h : n.isText = false) : (f.takes n).text = "" := by
  cases n with
  | text t => simp [Node.isText] at h
  | elem name attrs kids => simp [Frame.takes, flush_text]

private theorem takes_name (f : Frame) (n : Node) : (f.takes n).name = f.name := by
  cases n <;> simp [Frame.takes, flush_name]

private theorem takes_attrs (f : Frame) (n : Node) : (f.takes n).attrs = f.attrs := by
  cases n <;> simp [Frame.takes, flush_attrs]

private theorem kidsL_head (ks : List Node) (h : startsText ks = false) (rest : List Char)
    (hrest : ∀ c ∈ rest.head?, c = '<') : ∀ c ∈ (kidsL ks ++ rest).head?, c = '<' := by
  cases ks with
  | nil => simpa [kidsL_nil] using hrest
  | cons k ks =>
    cases k with
    | text t => simp [startsText, Node.isText] at h
    | elem name attrs kids =>
      intro c hc
      simp only [kidsL_cons, nodeL_elem] at hc
      split at hc <;> simp at hc <;> exact hc.symm

private theorem depth_le_of_mem (l : List Node) (k : Node) (h : k ∈ l) : k.depth ≤ Node.depthList l := by
  induction l with
  | nil => simp at h
  | cons n rest ih =>
    simp only [Node.depthList]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- A node's spelling at the reader's position reads back as the node,
handed to the state. -/
private def NodeReads (R : List Char) (bud : Budget) (n : Node) : Prop :=
  ∀ (s : State) (rest : List Char), R.drop s.pos = nodeL n ++ rest → CanonNode bud n →
    (n.isText = true → (∃ (stk : Array Frame) (f : Frame), s.stack = stk.push f ∧ f.text = "") ∧
      ∀ c ∈ rest.head?, c = '<') →
    ¬ (s.stack.isEmpty = true ∧ s.root.isSome = true) →
    s.stack.size + n.depth ≤ bud.depth → s.nodes + n.ticks ≤ bud.nodes →
    ∃ k m, k ≤ n.ticks ∧ Reach bud (bytesOf R) s ((bump (s.take n) k).at (s.pos + (nodeL n).length)) m

/-- A list of kids' spelling, read into the open element. -/
private def KidsReads (R : List Char) (bud : Budget) (ks : List Node) : Prop :=
  ∀ (s : State) (stk : Array Frame) (f : Frame) (rest : List Char),
    s.stack = stk.push f → (f.text = "" ∨ startsText ks = false) →
    R.drop s.pos = kidsL ks ++ rest → (∀ c ∈ rest.head?, c = '<') → CanonKids bud ks →
    stk.size + 1 + Node.depthList ks ≤ bud.depth → s.nodes + Node.ticksList ks ≤ bud.nodes →
    ∃ f' k m, k ≤ Node.ticksList ks ∧
      Reach bud (bytesOf R) s
        { s with stack := stk.push f', nodes := s.nodes + k, pos := s.pos + (kidsL ks).length } m ∧
      f'.name = f.name ∧ f'.attrs = f.attrs ∧ f'.flush.kids = f.flush.kids ++ ks.toArray

private theorem text_node_reads (R : List Char) (hl : Ascii R) (bud : Budget) (t : String) :
    NodeReads R bud (.text t) := by
  unfold NodeReads
  intro s rest hR hc htext _ _ hnodes
  obtain ⟨hne, hx, hb⟩ := hc
  obtain ⟨⟨stk, f, hs, hf⟩, hnext⟩ := htext rfl
  simp only [Node.ticks] at hnodes
  have hlen : t.toList.length = t.length := String.length_toList
  obtain ⟨k, m, hk, hreach⟩ := text_reads R hl bud (t.toList.length + 1) t.toList s stk f rest
    (by omega) hs (by simpa [nodeL_text] using hR) hnext hx (by rw [hf, String.empty_append, String.ofList_toList]; exact hb)
    (by omega)
  refine ⟨k, m, by simp only [Node.ticks]; omega, ?_⟩
  apply hreach.cast
  simp only [State.take, chars_push s stk f hs, bump, State.at, nodeL_text, String.ofList_toList]

private theorem kids_reads (R : List Char) (bud : Budget) :
    ∀ (ks : List Node), (∀ k ∈ ks, NodeReads R bud k) → KidsReads R bud ks := by
  intro ks
  induction ks with
  | nil =>
    intro _
    unfold KidsReads
    intro s stk f rest hs _ _ _ _ _ _
    refine ⟨f, 0, 0, Nat.le_refl _, ?_, rfl, rfl, by simp⟩
    apply (Reach.refl s).cast
    obtain ⟨pos, stack, root, nodes, doctype⟩ := s
    simp only at hs
    subst hs
    simp [kidsL_nil]
  | cons k ks ih =>
    intro hall
    unfold KidsReads
    intro s stk f rest hs hclean hR hnext hc hdepth hnodes
    obtain ⟨hck, hcks, hadj⟩ := hc
    have hk := hall k (by simp)
    unfold NodeReads at hk
    have hR' : R.drop s.pos = nodeL k ++ (kidsL ks ++ rest) := by rw [hR]; simp [kidsL_cons]
    have hclean_k : k.isText = true → f.text = "" := by
      intro ht
      rcases hclean with h | h
      · exact h
      · simp [startsText, ht] at h
    have hpre : k.isText = true → (∃ (stk' : Array Frame) (f' : Frame), s.stack = stk'.push f' ∧ f'.text = "") ∧
        ∀ c ∈ (kidsL ks ++ rest).head?, c = '<' :=
      fun ht => ⟨⟨stk, f, hs, hclean_k ht⟩, kidsL_head ks (hadj ht) rest hnext⟩
    have hroot : ¬ (s.stack.isEmpty = true ∧ s.root.isSome = true) := by rw [hs]; simp
    have hdk : s.stack.size + k.depth ≤ bud.depth := by
      rw [hs, Array.size_push]; simp only [Node.depthList] at hdepth; omega
    have hnk : s.nodes + k.ticks ≤ bud.nodes := by simp only [Node.ticksList] at hnodes; omega
    obtain ⟨k1, m1, hk1, r1⟩ := hk s (kidsL ks ++ rest) hR' hck hpre hroot hdk hnk
    let s₁ := (bump (s.take k) k1).at (s.pos + (nodeL k).length)
    have hs₁ : s₁.stack = stk.push (f.takes k) := by
      simp only [s₁, State.at, bump, take_push s stk f hs]
    have hR₁ : R.drop s₁.pos = kidsL ks ++ rest := drop_append_of R s.pos (nodeL k) _ hR'
    have hclean₁ : (f.takes k).text = "" ∨ startsText ks = false := by
      cases ht : k.isText with
      | true => exact Or.inr (hadj ht)
      | false => exact Or.inl (takes_clean f k ht)
    have hdepth₁ : stk.size + 1 + Node.depthList ks ≤ bud.depth := by
      simp only [Node.depthList] at hdepth; omega
    have hnodes₁ : s₁.nodes + Node.ticksList ks ≤ bud.nodes := by
      simp only [s₁, State.at, bump, take_push s stk f hs]
      simp only [Node.ticksList] at hnodes; omega
    obtain ⟨f', k2, m2, hk2, r2, hname, hattrs, hflush⟩ :=
      ih (fun x hx => hall x (by simp [hx])) s₁ stk (f.takes k) rest hs₁ hclean₁ hR₁ hnext hcks hdepth₁ hnodes₁
    refine ⟨f', k1 + k2, m2 + m1, by simp only [Node.ticksList]; omega, ?_, ?_, ?_, ?_⟩
    · apply (r1.trans r2).cast
      simp only [s₁, State.at, bump, take_push s stk f hs, kidsL_cons, List.length_append]
      congr 1 <;> omega
    · rw [hname, takes_name]
    · rw [hattrs, takes_attrs]
    · have hne : ∀ t, k = .text t → t ≠ "" := by
        intro t ht; subst ht; exact hck.1
      rw [hflush, takes_flush f k hclean_k hne]
      simp

private theorem give_at (s : State) (p : Nat) (n : Node) : (s.at p).give n = (s.give n).at p := by
  obtain ⟨pos, stack, root, nodes, doctype⟩ := s
  simp only [State.give, State.at]
  split <;> rfl

private theorem elem_reads (R : List Char) (hl : Ascii R) (bud : Budget) (name : String)
    (attrs : Array (String × String)) (kids : Array Node) (hk : KidsReads R bud kids.toList) :
    NodeReads R bud (.elem name attrs kids) := by
  unfold NodeReads
  intro s rest hR hc _ hroot hdepth hnodes
  obtain ⟨hn, hnb, hattrs, hnd, hkids⟩ := hc
  simp only [Node.depth] at hdepth
  simp only [Node.ticks] at hnodes
  by_cases he : kids.isEmpty = true
  · have hk0 : kids = #[] := by simpa using he
    subst hk0
    have hR' : R.drop s.pos = '<' :: (name.toList ++ (attrsL attrs.toList ++ (tagEnd true ++ rest))) := by
      rw [hR]; simp [nodeL_elem, tagEnd]
    have hstep := step_start R hl bud s name attrs.toList true rest hR' hn hnb hattrs hnd hroot
      (by simp [Node.ticksList] at hnodes; omega) (by simp [Node.depthList] at hdepth; omega)
    simp only [↓reduceIte, Array.toArray_toList] at hstep
    refine ⟨1, 1, by simp [Node.ticks, Node.ticksList], ?_⟩
    apply (Reach.single hstep (by simp [State.at]; omega)).cast
    simp only [State.take, give_bump, nodeL_elem, Array.isEmpty_empty, ↓reduceIte, List.length_cons,
      List.length_append, List.length_nil, tagEnd]
    congr 1
    omega
  · have hR' : R.drop s.pos = '<' :: (name.toList ++ (attrsL attrs.toList ++ (tagEnd false ++
        (kidsL kids.toList ++ ('<' :: '/' :: (name.toList ++ ('>' :: rest))))))) := by
      rw [hR]; simp [nodeL_elem, he, tagEnd]
    have hstep := step_start R hl bud s name attrs.toList false _ hR' hn hnb hattrs hnd hroot
      (by omega) (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte, Array.toArray_toList] at hstep
    let j := s.pos + 1 + name.toList.length + (attrsL attrs.toList).length + (tagEnd false).length
    let fr : Frame := { name, attrs, kids := #[], text := "" }
    let s₁ := (bump s 1).openAt fr j
    have hs₁ : s₁.stack = s.stack.push fr := rfl
    have hR₁ : R.drop s₁.pos = kidsL kids.toList ++ ('<' :: '/' :: (name.toList ++ ('>' :: rest))) := by
      have h1 := drop_append_of R s.pos ['<'] _ (by rw [hR']; rfl)
      have h2 := drop_append_of R _ name.toList _ h1
      have h3 := drop_append_of R _ (attrsL attrs.toList) _ h2
      have h4 := drop_append_of R _ (tagEnd false) _ h3
      simpa [s₁, State.openAt, j, Nat.add_assoc] using h4
    unfold KidsReads at hk
    obtain ⟨f', k, m, hkb, hreach, hname, hattrs', hflush⟩ :=
      hk s₁ s.stack fr _ hs₁ (Or.inl rfl) hR₁ (by simp) hkids (by omega)
        (by simp only [s₁, State.openAt, bump]; omega)
    let s₂ : State :=
      { s₁ with stack := s.stack.push f', nodes := s₁.nodes + k, pos := s₁.pos + (kidsL kids.toList).length }
    have hR₂ : R.drop s₂.pos = '<' :: '/' :: (name.toList ++ ('>' :: rest)) :=
      drop_append_of R s₁.pos _ _ hR₁
    have hend := step_end R hl bud s₂ name rest f' hR₂ hn hnb (by simp [s₂, Array.back?_push])
      (by rw [hname])
    have hclose : f'.close = .elem name attrs kids := by
      unfold Frame.close
      simp only [flush_name, flush_attrs, hname, hattrs', hflush]
      simp [fr, Frame.flush]
    refine ⟨k + 1, 1 + m + 1, by simp only [Node.ticks]; omega, ?_⟩
    have r := Reach.cons hstep (by simp [State.openAt]; omega)
      (hreach.trans (Reach.single hend (by simp [s₂, State.closeAt, State.at]; omega)))
    apply r.cast
    simp only [State.closeAt, hclose, State.take]
    have hpop : s₂.popped = (bump s (1 + k)).at (s₁.pos + (kidsL kids.toList).length) := by
      simp only [s₂, s₁, State.popped, State.openAt, bump, State.at, Array.pop_push]
      congr 1
      omega
    rw [hpop, give_at, give_bump]
    simp only [State.at, bump, nodeL_elem, he, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      List.length_append, s₂, s₁, State.openAt, j, tagEnd, List.length_nil]
    congr 1 <;> omega

/-- **Every tree's spelling reads back as the tree**, by depth. -/
private theorem all_reads (R : List Char) (hl : Ascii R) (bud : Budget) :
    ∀ (D : Nat) (n : Node), n.depth ≤ D → NodeReads R bud n := by
  intro D
  induction D with
  | zero =>
    intro n hn
    cases n with
    | text t => exact text_node_reads R hl bud t
    | elem name attrs kids => simp [Node.depth] at hn
  | succ D ih =>
    intro n hn
    cases n with
    | text t => exact text_node_reads R hl bud t
    | elem name attrs kids =>
      apply elem_reads R hl bud name attrs kids
      apply kids_reads R bud kids.toList
      intro k hk
      apply ih k
      have := depth_le_of_mem kids.toList k hk
      simp only [Node.depth] at hn
      omega

/-! ## The spelling's characters -/

/-- Characters a reader reads one byte each, none a control. -/
private def Plain (l : List Char) : Prop := ∀ c ∈ l, 32 ≤ c.toNat ∧ c.toNat ≤ 126

private theorem plain_append {a b : List Char} (ha : Plain a) (hb : Plain b) : Plain (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h
  · exact hb c h

private theorem plain_cons {c : Char} {l : List Char} (hc : 32 ≤ c.toNat ∧ c.toNat ≤ 126) (hl : Plain l) :
    Plain (c :: l) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | h
  · exact hc
  · exact hl d h

private theorem plain_refL (c : Char) : Plain (refL c) := by
  intro d hd
  simp only [refL, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | h | rfl
  · decide
  · decide
  · have := toDigits_digit c.toNat d h; omega
  · decide

private theorem plain_escL (l : List Char) : Plain (escL l) := by
  induction l with
  | nil => intro c hc; simp [escL] at hc
  | cons c rest ih =>
    rw [escL_cons]
    apply plain_append _ ih
    unfold pieceL
    split
    · next h =>
      have := literal_toNat c h
      exact plain_cons ⟨this.1, this.2.1⟩ (by intro d hd; simp at hd)
    · exact plain_refL c

private theorem plain_name (name : String) (hn : CanonName name) : Plain name.toList := by
  intro c hc
  have hb := hn.2.1 c hc
  have ha := hn.2.2 c hc
  simp only [nameByte, nameStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  omega

private theorem plain_attrsL (attrs : List (String × String)) (h : ∀ kv ∈ attrs, CanonAttr bud kv) :
    Plain (attrsL attrs) := by
  induction attrs with
  | nil => intro c hc; simp [attrsL] at hc
  | cons kv rest ih =>
    rw [attrsL_cons]
    have hkv := h kv (by simp)
    refine plain_cons (by decide) (plain_append (plain_name kv.1 hkv.1) (plain_cons (by decide)
      (plain_cons (by decide) (plain_append (plain_escL _) (plain_cons (by decide)
        (ih fun x hx => h x (by simp [hx])))))))

private theorem plain_nodeL (bud : Budget) : ∀ (D : Nat) (n : Node), n.depth ≤ D → CanonNode bud n → Plain (nodeL n) := by
  intro D
  induction D with
  | zero =>
    intro n hn hc
    cases n with
    | text t => rw [nodeL_text]; exact plain_escL _
    | elem name attrs kids => simp [Node.depth] at hn
  | succ D ih =>
    intro n hn hc
    cases n with
    | text t => rw [nodeL_text]; exact plain_escL _
    | elem name attrs kids =>
      obtain ⟨hname, _, hattrs, _, hkids⟩ := hc
      have hks : ∀ ks : List Node, (∀ k ∈ ks, k ∈ kids.toList) → CanonKids bud ks → Plain (kidsL ks) := by
        intro ks
        induction ks with
        | nil => intro _ _ c hc; simp [kidsL_nil] at hc
        | cons k ks ihk =>
          intro hsub hck
          rw [kidsL_cons]
          apply plain_append
          · apply ih k _ hck.1
            have := depth_le_of_mem kids.toList k (hsub k (by simp))
            simp only [Node.depth] at hn
            omega
          · exact ihk (fun x hx => hsub x (by simp [hx])) hck.2.1
      have hk := hks kids.toList (fun _ h => h) hkids
      have hnm := plain_name name hname
      have hat := plain_attrsL attrs.toList hattrs
      rw [nodeL_elem]
      split
      · exact plain_cons (by decide) (plain_append hnm (plain_append hat (by
          intro c hc; simp at hc; rcases hc with rfl | rfl <;> decide)))
      · exact plain_cons (by decide) (plain_append hnm (plain_append hat (plain_cons (by decide)
          (plain_append hk (plain_cons (by decide) (plain_cons (by decide) (plain_append hnm
            (by intro c hc; simp at hc; subst hc; decide))))))))

private theorem ascii_of_plain {l : List Char} (h : Plain l) : Ascii l := fun c hc => by
  have := h c hc; omega

/-! ## The document -/

private theorem toList_xmlDecl : "<?xml".toList = ['<', '?', 'x', 'm', 'l'] := by decide

private theorem xmlDecl_toUTF8 : "<?xml".toUTF8 = bytesOf ['<', '?', 'x', 'm', 'l'] := by
  rw [toUTF8_ascii _ (by rw [toList_xmlDecl]; intro c hc; simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide),
    toList_xmlDecl]

/-- **A spelling that opens with a tag is UTF-8 with no declaration.** -/
private theorem decode_tag (R : List Char) (hl : Ascii R) (c : Char) (rest : List Char) (hR : R = '<' :: c :: rest)
    (hc : nameStart c.toNat = true) : decode (bytesOf R) = .ok (bytesOf R, 0) := by
  have h0 : at? (bytesOf R) 0 = 60 := by rw [at?_bytesOf R 0 hl, hR]; rfl
  have h1 : at? (bytesOf R) 1 = c.toNat := by rw [at?_bytesOf R 1 hl, hR]; rfl
  have hcn : c.toNat ≠ 0 ∧ c.toNat ≠ 63 := by
    simp only [nameStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    omega
  have hxml : bytesAt (bytesOf R) 0 "<?xml" = false := by
    cases h : bytesAt (bytesOf R) 0 "<?xml" with
    | false => rfl
    | true =>
      have := (bytesAt_spec _ _ _ h).2 1 (by rw [xmlDecl_toUTF8, size_bytesOf]; decide)
      rw [Nat.zero_add, h1, xmlDecl_toUTF8, at?_bytesOf _ _ (by
        intro c hc; simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide)] at this
      exact absurd this hcn.2
  have hb1 : (c.toNat == 0) = false := by simpa using hcn.1
  unfold decode
  simp only [h0, h1, hxml, hb1, show ((60 : Nat) == 0) = false from rfl, show ((60 : Nat) == 255) = false from rfl,
    show ((60 : Nat) == 60) = true from rfl, show ((60 : Nat) == 239) = false from rfl,
    show ((60 : Nat) == 254) = false from rfl, Bool.false_and, Bool.and_false, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  rfl

private theorem forIn'_yield {β : Type} : ∀ (l : List Nat) (init : β) (f : (a : Nat) → a ∈ l → β → Id (ForInStep β)),
    (∀ a ha, f a ha init = pure (.yield init)) → forIn' l init f = pure init := by
  intro l
  induction l with
  | nil => intro init f _; rfl
  | cons a as ih =>
    intro init f h
    rw [List.forIn'_cons, h a List.mem_cons_self]
    exact ih init _ (fun a' ha' => h a' (List.mem_cons_of_mem a ha'))

/-- **No character of a printable spelling is one XML refuses.** -/
private theorem badCharAt_plain (l : List Char) (hp : Plain l) : badCharAt (bytesOf l) = none := by
  unfold badCharAt
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [forIn'_yield]
  · rfl
  · intro i hi
    have hi' : i < l.length := by
      simp [List.mem_range'_1, size_bytesOf, Std.Legacy.Range.size] at hi
      omega
    have hv : (bytesOf l)[i]'(by rw [size_bytesOf]; exact hi') = UInt8.ofNat l[i].toNat := by
      simp [bytesOf]
    have hc := hp l[i] (List.getElem_mem hi')
    have hn : ((bytesOf l)[i]'(by rw [size_bytesOf]; exact hi')).toNat = l[i].toNat := by
      rw [hv, UInt8.toNat_ofNat']; omega
    simp only [hn]
    have h1 : (decide (l[i].toNat < 32) && l[i].toNat != 9 && l[i].toNat != 10 && l[i].toNat != 13) = false := by
      simp; omega
    have h2 : (l[i].toNat == 239) = false := by simp; omega
    simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- What the round trip asks of a tree: an element the reader reads back
as it stands, within the budget. -/
@[expose] public def Canon (bud : Budget) (n : Node) : Prop :=
  n.isText = false ∧ CanonNode bud n ∧ n.depth ≤ bud.depth ∧ n.ticks ≤ bud.nodes ∧ (render n).size ≤ bud.bytes

/-- **The reader reads a rendered tree back as it stands.** -/
public theorem parseWith_render_id (bud : Budget) (n : Node) (h : Canon bud n) : parseWith bud (render n) = .ok n := by
  obtain ⟨htext, hc, hdepth, hticks, hsize⟩ := h
  have hp : Plain (nodeL n) := plain_nodeL bud n.depth n (Nat.le_refl _) hc
  have hl : Ascii (nodeL n) := ascii_of_plain hp
  have hrender : render n = bytesOf (nodeL n) := by
    unfold render
    rw [toUTF8_ascii _ (by rw [renderOne_toList]; simpa using hl), renderOne_toList]
    rfl
  cases n with
  | text t => simp [Node.isText] at htext
  | elem name attrs kids =>
    have hn : CanonName name := hc.1
    obtain ⟨c, cs, hcs, hstart⟩ := hn.1
    have hhead : ∃ tail, nodeL (.elem name attrs kids) = '<' :: c :: tail := by
      rw [nodeL_elem]; split <;> exact ⟨_, by rw [hcs]; rfl⟩
    obtain ⟨tail, htail⟩ := hhead
    rw [hrender]
    unfold parseWith
    have hsz : ¬ ((bytesOf (nodeL (.elem name attrs kids))).size > bud.bytes) := by rw [← hrender]; omega
    simp only [hsz, ↓reduceIte, decode_tag _ hl c tail htail hstart, validateUTF8_bytesOf _ hl, Bool.not_true,
      Bool.false_eq_true, badCharAt_plain _ hp]
    have hreads := all_reads (nodeL (.elem name attrs kids)) hl bud _ (.elem name attrs kids) (Nat.le_refl _)
    unfold NodeReads at hreads
    obtain ⟨k, m, _, hreach⟩ := hreads { pos := 0, stack := #[], root := none, nodes := 0, doctype := false } []
      (by simp) hc (by intro h; simp [Node.isText] at h) (by simp) (by simpa using hdepth) (by simpa using hticks)
    rw [run_reach hreach (by simp [State.at, size_bytesOf])]
    simp [State.take, give_root, State.at, bump, size_bytesOf]

/-- **The reader reads a rendered tree back as it stands**, under the
standard budget. -/
public theorem parse_render_id (n : Node) (h : Canon Budget.standard n) : parse (render n) = .ok n :=
  parseWith_render_id Budget.standard n h

end LeanTex.Core.Xml
