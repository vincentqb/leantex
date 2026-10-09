module

public import LeanTex.Core.PdfContentLex
public import LeanTex.Core.PdfObjProof
import all LeanTex.Core.PdfContentLex
import all LeanTex.Core.PdfLex
import all LeanTex.Core.PdfObj
import LeanTex.Core.PdfObjSpelling
import LeanTex.Core.PdfReadProof
import LeanTex.Core.PdfLexProof
import LeanTex.Core.PdfLexBoundary
import LeanTex.Core.LoopProgress
import LeanTex.Core.PdfNumber

/-!
# The content tokenizer reads back what its writer spells

`scan_render_exact`: tokens the writer spells (`Spelled`) come back from
`render` whole and in order. The proof follows the actual scanner, step by
step (`scan_stops`, progress-indexed over the token list): at each token's
first byte the step reads exactly the token — a number by `scanNumber`, a
word by `runEnd`, an object by the object reader's own round trip
(`parseVal_render_span_exact`) — and stops at its line feed; the byte after
it is where the next begins (`skip_after`), and the object reader's
reference lookahead never closes there (`tryRef_after`), the reference
marker standing only as an operator's first letter.
-/

namespace LeanTex.Core.PdfContentLex

open LeanTex.Core.PdfLex LeanTex.Core.PdfRead

/-! ## Lemmas -/

theorem runEnd_stops {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i cs) (hr : ∀ c ∈ cs, regular c = true)
    (he : regular (at? b (i + cs.length)) = false) :
    Loop.Stops (fun j => pure (if regular (at? b j) then ForInStep.yield (j + 1) else .done j))
      i (cs.length + 1) (i + cs.length) := by
  induction cs generalizing i with
  | nil =>
    apply Loop.Stops.done
    simp only [List.length_nil, Nat.add_zero] at he ⊢
    simp [he]
  | cons c cs ih =>
    have hc : regular (at? b i) = true := by rw [h.head]; exact hr c (by simp)
    have ht := ih h.tail (fun d hd => hr d (by simp [hd]))
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he)
    have hh := Loop.Stops.yield
      (step := fun j => pure (if regular (at? b j) then ForInStep.yield (j + 1) else .done j))
      (a := i) (b := i + 1) (by simp [hc]) ht
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem runEnd_exact {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i cs) (hr : ∀ c ∈ cs, regular c = true)
    (he : regular (at? b (i + cs.length)) = false) :
    runEnd b i = i + cs.length := by
  unfold runEnd
  exact Loop.forIn_range_stops_exact (runEnd_stops h hr he) (b.size + 1)
    (by have := h.bound; omega)

theorem asciiAt_exact {b : ByteArray} {i : Nat} {cs : List Nat} (h : Span b i cs) :
    asciiAt b i (i + cs.length) = String.ofList (cs.map Char.ofNat) := by
  unfold asciiAt
  congr 1
  rw [Nat.add_sub_cancel_left]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [h.byte k (by simpa using h2)]

/-- An operator's bytes read back as its characters. -/
theorem ascii_name (n : String) :
    String.ofList ((n.toList.map Char.toNat).map Char.ofNat) = n := by
  rw [List.map_map]
  have : (Char.ofNat ∘ Char.toNat) = id := by
    funext c; simp [Char.ofNat_toNat]
  rw [this, List.map_id, String.ofList_toList]

theorem tryRef_none_of {b : ByteArray} {i0 : Nat}
    (hk : ∀ gen j, parseUInt b (skipWs b i0) = some (gen, j) →
      at? b (skipWs b j) = 82 → regular (at? b (skipWs b j + 1)) = true) :
    tryRef b i0 = none := by
  unfold tryRef
  cases hp : parseUInt b (skipWs b i0) with
  | none => rfl
  | some r =>
    obtain ⟨gen, j⟩ := r
    simp only [bind, Option.bind]
    by_cases hr : at? b (skipWs b j) = 82
    · have hreg := hk gen j hp hr
      simp only [regular, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        bne_iff_ne, ne_eq] at hreg
      simp [hr, hreg.1.1, hreg.1.2, hreg.2]
    · simp [hr]


/-! ## The writer's tokens -/

/-- An operator the writer spells: regular ASCII characters, the first no
number's, not a word the tokenizer reads itself nor the reference marker. -/
public structure OpSpelled (n : String) : Prop where
  ne : n.toList ≠ []
  ascii : ∀ c ∈ n.toList, c.toNat < 128
  reg : ∀ c ∈ n.toList, regular c.toNat = true
  lead : ∀ c, n.toList.head? = some c → numByte c.toNat = false
  word : n ≠ "true" ∧ n ≠ "false" ∧ n ≠ "null" ∧ n ≠ "BI" ∧ n ≠ "R"

/-- An operand the writer spells: one the object writer spells, other than
a reference — a content stream holds none (§7.8.2). -/
public def ValSpelled (o : Obj) : Prop := o.Representable ∧ ∀ n g, o ≠ .ref n g

/-- Whether the object reader reads an operand: a string, a name, an
array, a dictionary. -/
@[expose] public def readByObj : Obj → Bool
  | .str _ | .name _ | .arr _ | .dict _ => true
  | .null | .bool _ | .int _ | .real _ | .ref _ _ => false

/-- An operator spelled with a leading `R`. -/
@[expose] public def leadR : Tok → Bool
  | .op n => n.toList.head? == some 'R'
  | .val _ | .inline _ _ => false

/-- A token the writer spells. -/
@[expose] public def TokSpelled : Tok → Prop
  | .val o => ValSpelled o
  | .op n => OpSpelled n
  | .inline _ _ => False

/-- **Tokens the writer spells** so that `scan` reads them back: each token
spelled, and no operand the object reader reads followed by an operator
spelled with a leading `R` — what the reader's reference lookahead would
otherwise need to rule out (the writer's `RG` follows numbers only). -/
public def Spelled : List Tok → Prop
  | [] => True
  | t :: rest => TokSpelled t ∧
    (∀ o, t = .val o → readByObj o = true → ∀ u ∈ rest.head?, leadR u = false) ∧ Spelled rest

/-- A token's bytes. -/
@[expose] public def spell : Tok → ByteArray
  | .val o => o.render
  | .op n => n.toUTF8
  | .inline d data => Tok.renderInto ByteArray.empty (.inline d data)

/-- Tokens spelled onto `acc`, a line feed after each. -/
@[expose] public def renderLInto (acc : ByteArray) : List Tok → ByteArray
  | [] => acc
  | t :: ts => renderLInto ((acc ++ spell t).push 10) ts

/-- Tokens spelled one after another, a line feed after each. -/
@[expose] public def renderL (ts : List Tok) : ByteArray := renderLInto ByteArray.empty ts

theorem push_nl (a : ByteArray) : a.push 10 = a ++ ⟨#[10]⟩ := by
  apply ByteArray.ext
  simp [ByteArray.data_push, ByteArray.data_append]

theorem renderLInto_acc (acc : ByteArray) (ts : List Tok) :
    renderLInto acc ts = acc ++ renderL ts := by
  induction ts generalizing acc with
  | nil => simp [renderLInto, renderL]
  | cons t ts ih =>
    simp only [renderL, renderLInto]
    rw [ih, ih ((ByteArray.empty ++ spell t).push 10)]
    simp only [push_nl, ByteArray.empty_append, ByteArray.append_assoc]

@[simp] theorem renderL_nil : renderL [] = ByteArray.empty := rfl

theorem renderL_cons (t : Tok) (ts : List Tok) :
    renderL (t :: ts) = spell t ++ ⟨#[10]⟩ ++ renderL ts := by
  simp only [renderL, renderLInto]
  rw [renderLInto_acc]
  simp only [push_nl, ByteArray.empty_append, renderL]

theorem renderInto_spell (acc : ByteArray) (t : Tok) (ht : TokSpelled t) :
    t.renderInto acc = acc ++ spell t := by
  cases t with
  | val o => simp [Tok.renderInto, spell]
  | op n => simp [Tok.renderInto, spell]
  | inline d data => exact absurd ht (by simp [TokSpelled])

theorem foldl_render (acc : ByteArray) (ts : List Tok) (h : ∀ t ∈ ts, TokSpelled t) :
    ts.foldl (fun acc t => (t.renderInto acc).push 10) acc = acc ++ renderL ts := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun u hu => h u (by simp [hu])), renderInto_spell acc t (h t (by simp))]
    simp only [renderL_cons]
    apply ByteArray.ext
    simp [ByteArray.data_append, ByteArray.data_push, Array.append_assoc]

theorem spelled_all {ts : List Tok} (h : Spelled ts) : ∀ t ∈ ts, TokSpelled t := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact ih h.2.2 u hu

theorem render_eq (toks : Array Tok) (h : Spelled toks.toList) : render toks = renderL toks.toList := by
  unfold render
  rw [← Array.foldl_toList, foldl_render ByteArray.empty toks.toList (spelled_all h)]
  simp

/-! ## First bytes -/

/-- What a spelled token's first byte tells the reader at its start. -/
structure Head (c : Nat) : Prop where
  ws : isWs c = false
  comment : c ≠ 37
  lt : c < 256

theorem numByte_head {c : Nat} (h : numByte c = true) : Head c ∧ c ≠ 82 := by
  have := number_byte h
  exact ⟨⟨this.2.1, this.2.2.1, by omega⟩, this.2.2.2.1⟩

theorem int_chars_num (n : Int) : ∀ c ∈ (toString n).toList, numByte c.toNat = true := by
  intro c hc
  rcases Number.int_chars n c hc with hd | rfl
  · have : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by simpa using Char.isDigit_iff_toNat.mp hd
    simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  · rfl

theorem octets_int (n : Int) : octets (Obj.int n).render = (toString n).toList.map Char.toNat := by
  have h := numeric_octets (toString n) (int_chars_num n)
  simpa [Obj.render, Obj.renderInto] using h

theorem octets_real (r : String) (h : Obj.RealSpelling r) :
    octets (Obj.real r).render = r.toList.map Char.toNat := by
  have := numeric_octets r h.2
  simpa [Obj.render, Obj.renderInto] using this

theorem octets_str (raw : ByteArray) : octets (Obj.str raw).render = octets raw := by
  simp [Obj.render, Obj.renderInto]

theorem octets_name (s : String) (hn : s ≠ "") :
    octets (Obj.name s).render = 47 :: (s.toList.flatMap nameChars).map Char.toNat := by
  have := Obj.name_octets s hn
  simpa [Obj.render, Obj.renderInto] using this

theorem octets_arr (xs : Array Obj) :
    octets (Obj.arr xs).render = 91 :: (octets (Obj.renderList ByteArray.empty xs.toList) ++ [93]) := by
  simp only [Obj.render, Obj.renderInto]
  rw [Obj.renderList_exact]
  simp [octets_push, octets_append]

theorem octets_dict (es : Array (String × Obj)) :
    octets (Obj.dict es).render =
      60 :: 60 :: 32 :: (octets (Obj.renderEntries ByteArray.empty es.toList) ++ [62, 62]) := by
  simp only [Obj.render, Obj.renderInto]
  rw [Obj.renderEntries_exact]
  simp [octets_append, String.toUTF8_eq_toByteArray]
  rfl

theorem octets_word (s : String) (h : ∀ c ∈ s.toList, c.toNat < 128) :
    octets s.toUTF8 = s.toList.map Char.toNat := by
  simpa using octets_ascii s.toList h


/-! ## One token read -/

theorem nl_size : (⟨#[10]⟩ : ByteArray).size = 1 := rfl

theorem nl_at (P S R : ByteArray) : at? (P ++ S ++ ⟨#[10]⟩ ++ R) (P.size + S.size) = 10 := by
  have e : P ++ S ++ ⟨#[10]⟩ ++ R = (P ++ S) ++ (⟨#[10]⟩ ++ R) := by
    simp only [ByteArray.append_assoc]
  rw [e]
  have h := at?_append_right (P ++ S) (⟨#[10]⟩ ++ R) 0
  simp only [ByteArray.size_append, Nat.add_zero] at h
  rw [h, at?_append_left _ _ _ (by rw [nl_size]; omega)]
  rfl

theorem span_tok (P S R : ByteArray) : Span (P ++ S ++ ⟨#[10]⟩ ++ R) P.size (octets S) := by
  have := Span.of_bytes P S (⟨#[10]⟩ ++ R)
  simpa [ByteArray.append_assoc, octets] using this

theorem at_after (P S R : ByteArray) (k : Nat) :
    at? (P ++ S ++ ⟨#[10]⟩ ++ R) (P.size + S.size + 1 + k) = at? R k := by
  have h := at?_append_right (P ++ S ++ ⟨#[10]⟩) R k
  simpa [ByteArray.size_append, Nat.add_assoc, nl_size] using h

theorem size_tok (P S R : ByteArray) :
    (P ++ S ++ ⟨#[10]⟩ ++ R).size = P.size + S.size + 1 + R.size := by
  simp [ByteArray.size_append, nl_size]

theorem regular_ws {c : Nat} (h : isWs c = true) : regular c = false := by
  simp [regular, h]

theorem objStart_not_regular {c : Nat} (h : regular c = true) : objStart c = false := by
  simp only [regular, isWs, isDelim, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_iff_ne, ne_eq] at h
  simp only [objStart, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  omega

/-- A run of regular ASCII characters that no number starts: what the
tokenizer reads as a word at a token's start. -/
structure Word (w : String) : Prop where
  ne : w.toList ≠ []
  ascii : ∀ c ∈ w.toList, c.toNat < 128
  reg : ∀ c ∈ w.toList, regular c.toNat = true
  lead : ∀ c, w.toList.head? = some c → numByte c.toNat = false

theorem OpSpelled.word' {n : String} (h : OpSpelled n) : Word n := ⟨h.ne, h.ascii, h.reg, h.lead⟩

/-- **A word at a token's start reads whole**: its first byte no number's,
no operand's, a regular one; its run ends at the line feed after it; its
bytes spell it. -/
theorem word_read {P R : ByteArray} {w : String} (hw : Word w) :
    let B := P ++ w.toUTF8 ++ ⟨#[10]⟩ ++ R
    ¬ B.size ≤ P.size ∧ numByte (at? B P.size) = false ∧ objStart (at? B P.size) = false ∧
      regular (at? B P.size) = true ∧ runEnd B P.size = P.size + w.toUTF8.size ∧
      asciiAt B P.size (P.size + w.toUTF8.size) = w ∧ P.size < P.size + w.toUTF8.size := by
  intro B
  have ho := octets_word w hw.ascii
  have hspan := span_tok P w.toUTF8 R
  rw [ho] at hspan
  have hlen : w.toUTF8.size = w.toList.length := by
    simpa using congrArg List.length ho
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, w.toList = c :: cs := by
    cases h : w.toList with
    | nil => exact absurd h hw.ne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hhead : at? B P.size = c.toNat := by
    have hs := hspan
    rw [hcs, List.map_cons] at hs
    exact hs.head
  have hreg : regular c.toNat = true := hw.reg c (by simp [hcs])
  have hend : regular (at? B (P.size + (w.toList.map Char.toNat).length)) = false := by
    rw [List.length_map, ← hlen]
    show regular (at? (P ++ w.toUTF8 ++ ⟨#[10]⟩ ++ R) (P.size + w.toUTF8.size)) = false
    rw [nl_at]
    rfl
  have hrun := runEnd_exact hspan (fun d hd => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact hw.reg e he) hend
  have hname := asciiAt_exact hspan
  rw [ascii_name, List.length_map, ← hlen] at hname
  rw [List.length_map, ← hlen] at hrun
  refine ⟨by show ¬ (P ++ w.toUTF8 ++ ⟨#[10]⟩ ++ R).size ≤ P.size; rw [size_tok]; omega,
    by rw [hhead]; exact hw.lead c (by simp [hcs]), by rw [hhead]; exact objStart_not_regular hreg,
    by rw [hhead]; exact hreg, hrun, hname, ?_⟩
  have : w.toList.length ≥ 1 := by rw [hcs]; simp
  omega

theorem step_op {P R : ByteArray} {n : String} (hn : OpSpelled n) {q : Nat}
    (hq : skipWs (P ++ n.toUTF8 ++ ⟨#[10]⟩ ++ R) q = P.size) (out : Array Tok) :
    step (P ++ n.toUTF8 ++ ⟨#[10]⟩ ++ R) { pos := q, out } =
      .yield { pos := P.size + n.toUTF8.size, out := out.push (.op n) } := by
  obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, hpos⟩ := word_read (P := P) (R := R) hn.word'
  unfold step
  simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname]
  obtain ⟨h1, h2, h3, h4, _⟩ := hn.word
  simp only [beq_iff_eq, h1, h2, h3, h4, ↓reduceIte]
  congr
  omega

theorem word_true : Word "true" := ⟨by decide, by decide, by decide, by decide⟩
theorem word_false : Word "false" := ⟨by decide, by decide, by decide, by decide⟩
theorem word_null : Word "null" := ⟨by decide, by decide, by decide, by decide⟩

theorem step_bool {P R : ByteArray} (v : Bool) {q : Nat}
    (hq : skipWs (P ++ spell (.val (.bool v)) ++ ⟨#[10]⟩ ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val (.bool v)) ++ ⟨#[10]⟩ ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val (.bool v))).size, out := out.push (.val (.bool v)) } := by
  cases v with
  | true =>
    have hs : spell (.val (.bool true)) = "true".toUTF8 := by simp [spell, Obj.render, Obj.renderInto]
    rw [hs] at hq ⊢
    obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, hpos⟩ := word_read (P := P) (R := R) word_true
    unfold step
    simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname, beq_self_eq_true]
  | false =>
    have hs : spell (.val (.bool false)) = "false".toUTF8 := by simp [spell, Obj.render, Obj.renderInto]
    rw [hs] at hq ⊢
    obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, hpos⟩ := word_read (P := P) (R := R) word_false
    unfold step
    simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname]
    simp

theorem step_null {P R : ByteArray} {q : Nat}
    (hq : skipWs (P ++ spell (.val .null) ++ ⟨#[10]⟩ ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val .null) ++ ⟨#[10]⟩ ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val .null)).size, out := out.push (.val .null) } := by
  have hs : spell (.val .null) = "null".toUTF8 := by simp [spell, Obj.render, Obj.renderInto]
  rw [hs] at hq ⊢
  obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, hpos⟩ := word_read (P := P) (R := R) word_null
  unfold step
  simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname]
  simp

theorem step_number {P R : ByteArray} {raw : String} {o : Obj}
    (hc : ∀ c ∈ raw.toList, numByte c.toNat = true) (hne : raw.toList ≠ [])
    (ho : numberObj raw = some o) {q : Nat}
    (hq : skipWs (P ++ raw.toUTF8 ++ ⟨#[10]⟩ ++ R) q = P.size) (out : Array Tok) :
    step (P ++ raw.toUTF8 ++ ⟨#[10]⟩ ++ R) { pos := q, out } =
      .yield { pos := P.size + raw.toUTF8.size, out := out.push (.val o) } := by
  have hoct := numeric_octets raw hc
  have hspan := span_tok P raw.toUTF8 R
  rw [hoct] at hspan
  have hlen : raw.toUTF8.size = raw.toList.length := numeric_size raw hc
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, raw.toList = c :: cs := by
    cases h : raw.toList with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hhead : at? (P ++ raw.toUTF8 ++ ⟨#[10]⟩ ++ R) P.size = c.toNat := by
    have hs := hspan
    rw [hcs, List.map_cons] at hs
    exact hs.head
  have hnum : numByte c.toNat = true := hc c (by simp [hcs])
  have hend : numByte (at? (P ++ raw.toUTF8 ++ ⟨#[10]⟩ ++ R) (P.size + raw.toList.length)) = false := by
    rw [← hlen, nl_at]
    rfl
  have hscan := scanNumber_exact hspan hc hend
  have hsz : ¬ (P ++ raw.toUTF8 ++ ⟨#[10]⟩ ++ R).size ≤ P.size := by
    rw [size_tok]; omega
  have hpos : P.size < P.size + raw.toList.length := by
    have : raw.toList.length ≥ 1 := by rw [hcs]; simp
    omega
  unfold step
  simp only [hq, hsz, ↓reduceIte, hhead, hnum, hscan, String.ofList_toList, ho, hlen]
  congr
  omega

theorem numberObj_int (n : Int) : numberObj (toString n) = some (.int n) := by
  unfold numberObj
  rw [Number.int_noDot, Number.int_toString_id]
  rfl

theorem numberObj_real (r : String) (h : Obj.RealSpelling r) : numberObj r = some (.real r) := by
  have : r.contains '.' = true := by
    rw [String.contains_char_eq]
    exact decide_eq_true h.1
  simp [numberObj, this]

theorem step_int {P R : ByteArray} (n : Int) {q : Nat}
    (hq : skipWs (P ++ spell (.val (.int n)) ++ ⟨#[10]⟩ ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val (.int n)) ++ ⟨#[10]⟩ ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val (.int n))).size, out := out.push (.val (.int n)) } := by
  have hs : spell (.val (.int n)) = (toString n).toUTF8 := by
    simp [spell, Obj.render, Obj.renderInto]
  rw [hs] at hq ⊢
  exact step_number (int_chars_num n) (Number.int_nonempty n) (numberObj_int n) hq out

theorem step_real {P R : ByteArray} (r : String) (hr : Obj.RealSpelling r) {q : Nat}
    (hq : skipWs (P ++ spell (.val (.real r)) ++ ⟨#[10]⟩ ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val (.real r)) ++ ⟨#[10]⟩ ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val (.real r))).size, out := out.push (.val (.real r)) } := by
  have hs : spell (.val (.real r)) = r.toUTF8 := by
    simp [spell, Obj.render, Obj.renderInto]
  rw [hs] at hq ⊢
  have hne : r.toList ≠ [] := by
    intro h; have := hr.1; rw [h] at this; simp at this
  exact step_number hr.2 hne (numberObj_real r hr) hq out



/-! ## What follows a token -/

/-- A spelled token's spelling opens with a byte that starts a token —
not white space, not a comment — and is the reference marker only as an
operator's first letter, a regular character after it. -/
theorem head_spell (u : Tok) (hu : TokSpelled u) :
    ∃ c cs, octets (spell u) = c :: cs ∧ isWs c = false ∧ c ≠ 37 ∧ c < 256 ∧
      (c = 82 → leadR u = true ∧ ∃ d ds, cs = d :: ds ∧ regular d = true) := by
  cases u with
  | inline d data => exact absurd hu (by simp [TokSpelled])
  | op n =>
    have hw := hu.word'
    have ho := octets_word n hw.ascii
    obtain ⟨c, cs, hcs⟩ : ∃ c cs, n.toList = c :: cs := by
      cases h : n.toList with
      | nil => exact absurd h hw.ne
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hreg : regular c.toNat = true := hw.reg c (by simp [hcs])
    have hreg' := hreg
    simp only [regular, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq] at hreg'
    refine ⟨c.toNat, cs.map Char.toNat, by show octets n.toUTF8 = _; rw [ho, hcs]; rfl,
      hreg'.1.2, ?_, ?_, ?_⟩
    · intro h; rw [h] at hreg'; simp [isDelim] at hreg'
    · have := hw.ascii c (by simp [hcs]); omega
    · intro h82
      have hc : c = 'R' := by
        have : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
        rw [this, h82]
      refine ⟨by simp [leadR, hcs, hc], ?_⟩
      cases hds : cs with
      | nil =>
        exfalso
        have : n = "R" := by
          have e := congrArg String.ofList hcs
          rw [String.ofList_toList] at e
          rw [e, hds, hc]
        exact hu.word.2.2.2.2 this
      | cons d ds =>
        exact ⟨d.toNat, ds.map Char.toNat, by simp, hw.reg d (by simp [hcs, hds])⟩
  | val o =>
    obtain ⟨hr, hnr⟩ := hu
    have plain : ∀ c cs, octets (spell (.val o)) = c :: cs → isWs c = false → c ≠ 37 → c < 256 →
        c ≠ 82 → ∃ c cs, octets (spell (.val o)) = c :: cs ∧ isWs c = false ∧ c ≠ 37 ∧ c < 256 ∧
          (c = 82 → leadR (.val o) = true ∧ ∃ d ds, cs = d :: ds ∧ regular d = true) :=
      fun c cs h h1 h2 h3 h4 => ⟨c, cs, h, h1, h2, h3, fun h5 => absurd h5 h4⟩
    have num : ∀ (s : String), octets (spell (.val o)) = s.toList.map Char.toNat → s.toList ≠ [] →
        (∀ c ∈ s.toList, numByte c.toNat = true) → ∃ c cs, octets (spell (.val o)) = c :: cs ∧
          isWs c = false ∧ c ≠ 37 ∧ c < 256 ∧
          (c = 82 → leadR (.val o) = true ∧ ∃ d ds, cs = d :: ds ∧ regular d = true) := by
      intro s hs hne hc
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, s.toList = c :: cs := by
        cases h : s.toList with
        | nil => exact absurd h hne
        | cons c cs => exact ⟨c, cs, rfl⟩
      have hb := number_byte (hc c (by simp [hcs]))
      exact plain c.toNat (cs.map Char.toNat) (by rw [hs, hcs]; rfl) hb.2.1 hb.2.2.1 (by omega) hb.2.2.2.1
    cases hr with
    | null =>
      exact plain 110 [117, 108, 108] (by simp [spell, Obj.render, Obj.renderInto]; rfl)
        (by decide) (by decide) (by decide) (by decide)
    | bool v =>
      cases v with
      | true =>
        exact plain 116 [114, 117, 101] (by simp [spell, Obj.render, Obj.renderInto]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | false =>
        exact plain 102 [97, 108, 115, 101] (by simp [spell, Obj.render, Obj.renderInto]; rfl)
          (by decide) (by decide) (by decide) (by decide)
    | int n =>
      exact num (toString n) (octets_int n) (Number.int_nonempty n) (int_chars_num n)
    | real hs =>
      exact num _ (octets_real _ hs) (by intro h; have := hs.1; rw [h] at this; simp at this) hs.2
    | @str raw hs =>
      have hoct : octets (spell (.val (.str raw))) = raw.data.toList.map UInt8.toNat := by
        rw [show spell (.val (.str raw)) = (Obj.str raw).render from rfl, octets_str]; rfl
      generalize raw.data.toList.map UInt8.toNat = l at hs hoct
      cases hs with
      | literal _ =>
        exact plain 40 _ (by rw [hoct]; rfl) (by decide) (by decide) (by decide) (by decide)
      | hex _ =>
        exact plain 60 _ (by rw [hoct]; rfl) (by decide) (by decide) (by decide) (by decide)
    | name hs =>
      exact plain 47 _ (octets_name _ hs.1) (by decide) (by decide) (by decide) (by decide)
    | arr _ =>
      exact plain 91 _ (octets_arr _) (by decide) (by decide) (by decide) (by decide)
    | dict _ _ =>
      exact plain 60 _ (octets_dict _) (by decide) (by decide) (by decide) (by decide)
    | ref n g =>
      exact absurd rfl (hnr n g)


theorem at_spell_head {Q R : ByteArray} {u : Tok} {c : Nat} {cs : List Nat}
    (h : octets (spell u) = c :: cs) :
    at? (Q ++ spell u ++ ⟨#[10]⟩ ++ R) Q.size = c := by
  have hs := span_tok Q (spell u) R
  rw [h] at hs
  exact hs.head

theorem at_spell_second {Q R : ByteArray} {u : Tok} {c d : Nat} {ds : List Nat}
    (h : octets (spell u) = c :: d :: ds) :
    at? (Q ++ spell u ++ ⟨#[10]⟩ ++ R) (Q.size + 1) = d := by
  have hs := span_tok Q (spell u) R
  rw [h] at hs
  exact hs.tail.head

/-- What stands where a list of spelled tokens begins: the end of the
input, or a token's first byte. -/
theorem renderL_head {Q : ByteArray} {rest : List Tok} (hs : ∀ t ∈ rest, TokSpelled t) :
    (at? (Q ++ renderL rest) Q.size = 256) ∨
      (isWs (at? (Q ++ renderL rest) Q.size) = false ∧ at? (Q ++ renderL rest) Q.size ≠ 37 ∧
        at? (Q ++ renderL rest) Q.size < 256 ∧
        (at? (Q ++ renderL rest) Q.size = 82 → regular (at? (Q ++ renderL rest) (Q.size + 1)) = true)) := by
  cases rest with
  | nil =>
    left
    simp only [renderL_nil, ByteArray.append_empty]
    exact at?_ge Q Q.size (Nat.le_refl _)
  | cons u rest' =>
    right
    obtain ⟨c, cs, hcs, hw, hc, hlt, hr⟩ := head_spell u (hs u (by simp))
    have e : Q ++ renderL (u :: rest') = Q ++ spell u ++ ⟨#[10]⟩ ++ renderL rest' := by
      simp only [renderL_cons, ByteArray.append_assoc]
    rw [e, at_spell_head hcs]
    refine ⟨hw, hc, hlt, fun h82 => ?_⟩
    obtain ⟨_, d, ds, hd, hreg⟩ := hr h82
    rw [hd] at hcs
    rw [at_spell_second hcs]
    exact hreg

/-- After a token's line feed, the reader stands where the next begins. -/
theorem skip_after {P S : ByteArray} {rest : List Tok} (hs : ∀ t ∈ rest, TokSpelled t) :
    skipWs (P ++ S ++ ⟨#[10]⟩ ++ renderL rest) (P.size + S.size) = P.size + S.size + 1 := by
  have hh := renderL_head (Q := P ++ S ++ ⟨#[10]⟩) hs
  have hq : (P ++ S ++ ⟨#[10]⟩).size = P.size + S.size + 1 := by simp [ByteArray.size_append, nl_size]
  rw [hq] at hh
  apply skipWs_whitespace_exact
  · rw [nl_at]; rfl
  · rcases hh with h | h
    · rw [h]; rfl
    · exact h.1
  · rcases hh with h | h
    · rw [h]; decide
    · exact h.2.1
  · rw [size_tok]; omega


theorem toString_ofNat_int (k : Nat) : toString (Int.ofNat k) = toString k := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  simp

theorem digit_not_numByte_false {c : Nat} (h : 48 ≤ c ∧ c ≤ 57) : numByte c = true := by
  simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- **After a token's line feed, no reference completes** — the reference
marker stands only as the first letter of an operator, a regular character
after it, so the reader's lookahead from there never closes one. -/
theorem tryRef_after {P S : ByteArray} {rest : List Tok} (hs : ∀ t ∈ rest, TokSpelled t) :
    tryRef (P ++ S ++ ⟨#[10]⟩ ++ renderL rest) (P.size + S.size) = none := by
  apply tryRef_none_of
  intro gen j hp h82
  rw [skip_after hs] at hp
  cases rest with
  | nil =>
    have h256 : at? (P ++ S ++ ⟨#[10]⟩ ++ renderL []) (P.size + S.size + 1) = 256 := by
      apply at?_ge; simp [ByteArray.size_append, nl_size]
    rw [parseUInt_none (by rw [h256]; omega)] at hp
    exact absurd hp (by simp)
  | cons u rest' =>
    have hsu : TokSpelled u := hs u (by simp)
    have hrest : ∀ t ∈ rest', TokSpelled t := fun t ht => hs t (by simp [ht])
    let Q := P ++ S ++ ⟨#[10]⟩
    have hQ : Q.size = P.size + S.size + 1 := by simp [Q, ByteArray.size_append, nl_size]
    have e : P ++ S ++ ⟨#[10]⟩ ++ renderL (u :: rest') = Q ++ spell u ++ ⟨#[10]⟩ ++ renderL rest' := by
      simp only [Q, renderL_cons, ByteArray.append_assoc]
    rw [e] at hp h82 ⊢
    rw [← hQ] at hp
    obtain ⟨c, cs, hcs, hw, hc, hlt, hr⟩ := head_spell u hsu
    have hhead := at_spell_head (Q := Q) (R := renderL rest') hcs
    -- A first byte that is no digit starts no unsigned integer.
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · cases u with
      | inline _ _ => exact absurd hsu (by simp [TokSpelled])
      | op m =>
        exfalso
        have hm := hsu.word'
        obtain ⟨c0, cs0, hcs0⟩ : ∃ c0 cs0, m.toList = c0 :: cs0 := by
          cases h : m.toList with
          | nil => exact absurd h hm.ne
          | cons c0 cs0 => exact ⟨c0, cs0, rfl⟩
        have ho := octets_word m hm.ascii
        rw [show spell (.op m) = m.toUTF8 from rfl, ho, hcs0] at hcs
        simp only [List.map_cons, List.cons.injEq] at hcs
        have := hm.lead c0 (by simp [hcs0])
        rw [← hcs.1] at hd
        rw [digit_not_numByte_false hd] at this
        exact absurd this (by simp)
      | val o =>
        obtain ⟨hro, hnr⟩ := hsu
        have hspan := span_tok Q (spell (.val o)) (renderL rest')
        have hnl := nl_at Q (spell (.val o)) (renderL rest')
        -- A head byte known to be no digit closes the case.
        have nodigit : ∀ d ds, octets (spell (.val o)) = d :: ds → ¬ (48 ≤ d ∧ d ≤ 57) → False := by
          intro d ds hdd hnd
          rw [hdd] at hcs
          simp only [List.cons.injEq] at hcs
          exact hnd (hcs.1 ▸ hd)
        cases hro with
        | null =>
          exact (nodigit 110 _ (by simp [spell, Obj.render, Obj.renderInto]; rfl) (by omega)).elim
        | bool v =>
          cases v with
          | true => exact (nodigit 116 _ (by simp [spell, Obj.render, Obj.renderInto]; rfl) (by omega)).elim
          | false => exact (nodigit 102 _ (by simp [spell, Obj.render, Obj.renderInto]; rfl) (by omega)).elim
        | @str raw hsr =>
          have hoct : octets (spell (.val (.str raw))) = raw.data.toList.map UInt8.toNat := by
            rw [show spell (.val (.str raw)) = (Obj.str raw).render from rfl, octets_str]; rfl
          generalize raw.data.toList.map UInt8.toNat = l at hsr hoct
          cases hsr with
          | literal _ => exact (nodigit 40 _ (by rw [hoct]; rfl) (by omega)).elim
          | hex _ => exact (nodigit 60 _ (by rw [hoct]; rfl) (by omega)).elim
        | name hn => exact (nodigit 47 _ (octets_name _ hn.1) (by omega)).elim
        | arr _ => exact (nodigit 91 _ (octets_arr _) (by omega)).elim
        | dict _ _ => exact (nodigit 60 _ (octets_dict _) (by omega)).elim
        | ref n g => exact absurd rfl (hnr n g)
        | int n =>
          cases n with
          | negSucc m =>
            exfalso
            have hstr : toString (Int.negSucc m) = "-" ++ toString (m + 1) := by
              simp [Int.toString_eq_repr, Int.repr_eq_ite]
            have ho := octets_int (Int.negSucc m)
            rw [hstr] at ho
            exact nodigit 45 ((toString (m + 1)).toList.map Char.toNat)
              (by rw [show spell (.val (.int (Int.negSucc m))) = (Obj.int (Int.negSucc m)).render from rfl, ho]
                  simp [String.toList_append]) (by omega)
          | ofNat k =>
            have hsp : octets (spell (.val (.int (Int.ofNat k)))) = octets (toString k).toUTF8 := by
              rw [show spell (.val (.int (Int.ofNat k))) = (Obj.int (Int.ofNat k)).render from rfl]
              show octets (ByteArray.empty ++ (toString (Int.ofNat k)).toUTF8) = _
              rw [ByteArray.empty_append, toString_ofNat_int]
            have hsz : (spell (.val (.int (Int.ofNat k)))).size = (toString k).toUTF8.size := by
              have := congrArg List.length hsp
              simpa using this
            rw [hsp] at hspan
            have hpn := parse_nat hspan (by rw [← hsz, hnl]; exact Or.inr (Or.inl rfl))
            rw [hpn] at hp
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨-, rfl⟩ := hp
            rw [← hsz, skip_after hrest] at h82 ⊢
            have hh := renderL_head (Q := Q ++ spell (.val (.int (Int.ofNat k))) ++ ⟨#[10]⟩) hrest
            have hq' : (Q ++ spell (.val (.int (Int.ofNat k))) ++ ⟨#[10]⟩).size =
                Q.size + (spell (.val (.int (Int.ofNat k)))).size + 1 := by
              simp [ByteArray.size_append, nl_size]
            rw [hq'] at hh
            rcases hh with h | h
            · rw [h] at h82; exact absurd h82 (by decide)
            · exact h.2.2.2 h82
        | @real r hrs =>
          exfalso
          have hoct : octets (spell (.val (.real r))) = r.toList.map Char.toNat := octets_real r hrs
          rw [hoct] at hspan
          have hsplit : r.toList = r.toList.takeWhile Char.isDigit ++ r.toList.dropWhile Char.isDigit :=
            List.takeWhile_append_dropWhile.symm
          have hdrop : r.toList.dropWhile Char.isDigit ≠ [] := by
            intro h0
            have hdot := hrs.1
            rw [hsplit, h0, List.append_nil] at hdot
            have := List.all_eq_true.mp (List.all_takeWhile (p := Char.isDigit) (l := r.toList)) '.' hdot
            exact absurd this (by decide)
          obtain ⟨c', more, hcm⟩ : ∃ c' more, r.toList.dropWhile Char.isDigit = c' :: more := by
            cases h : r.toList.dropWhile Char.isDigit with
            | nil => exact absurd h hdrop
            | cons c' more => exact ⟨c', more, rfl⟩
          have hc'nd : c'.isDigit = false := by
            have := List.head_dropWhile_not Char.isDigit (l := r.toList) hdrop
            simpa [hcm] using this
          have hc'num : numByte c'.toNat = true := hrs.2 c' (by rw [hsplit, hcm]; simp)
          have hdsdig : ∀ c ∈ r.toList.takeWhile Char.isDigit, c.isDigit = true :=
            fun c hc => List.all_eq_true.mp List.all_takeWhile c hc
          have hdsne : r.toList.takeWhile Char.isDigit ≠ [] := by
            intro h0
            have h1 : r.toList = c' :: more := by rw [hsplit, h0, hcm]; rfl
            rw [hoct, h1] at hcs
            simp only [List.map_cons, List.cons.injEq] at hcs
            have hdig : c'.isDigit = true := by
              rw [Char.isDigit_iff_toNat]; rw [hcs.1]; simpa using hd
            rw [hc'nd] at hdig; exact absurd hdig (by simp)
          rw [hsplit, hcm, List.map_append] at hspan
          have hspds := hspan.append_left
          have hat : at? (Q ++ spell (.val (.real r)) ++ ⟨#[10]⟩ ++ renderL rest')
              (Q.size + (r.toList.takeWhile Char.isDigit).length) = c'.toNat := by
            have := hspan.append_right
            simp only [List.length_map, List.map_cons] at this
            exact this.head
          have hpu := parseUInt_exact hspds hdsdig hdsne (by
            rw [hat]
            intro hh
            have : c'.isDigit = true := by rw [Char.isDigit_iff_toNat]; simpa using hh
            rw [hc'nd] at this; exact absurd this (by simp))
          rw [hpu] at hp
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨-, rfl⟩ := hp
          have hb := number_byte hc'num
          rw [skipWs_fixed_point (by rw [hat]; exact hb.2.1) (by rw [hat]; exact hb.2.2.1), hat] at h82
          exact hb.2.2.2.1 h82
    · rw [parseUInt_none (by rw [hhead]; exact hd)] at hp
      exact absurd hp (by simp)


theorem obj_head (o : Obj) (hro : o.Representable) (hb : readByObj o = true) :
    ∃ c cs, octets o.render = c :: cs ∧ numByte c = false ∧ objStart c = true ∧
      isWs c = false ∧ c ≠ 37 := by
  cases hro with
  | @str raw hsr =>
    have hoct : octets (Obj.str raw).render = raw.data.toList.map UInt8.toNat := by
      rw [octets_str]; rfl
    generalize raw.data.toList.map UInt8.toNat = l at hsr hoct
    cases hsr with
    | literal _ => exact ⟨40, _, hoct, by decide, by decide, by decide, by decide⟩
    | hex _ => exact ⟨60, _, hoct, by decide, by decide, by decide, by decide⟩
  | name hn => exact ⟨47, _, octets_name _ hn.1, by decide, by decide, by decide, by decide⟩
  | arr _ => exact ⟨91, _, octets_arr _, by decide, by decide, by decide, by decide⟩
  | dict _ _ => exact ⟨60, _, octets_dict _, by decide, by decide, by decide, by decide⟩
  | null => simp [readByObj] at hb
  | bool _ => simp [readByObj] at hb
  | int _ => simp [readByObj] at hb
  | real _ => simp [readByObj] at hb
  | ref _ _ => simp [readByObj] at hb

/-- The byte after an object operand's line feed is no reference marker: a
token spelled with one is an operator spelled with a leading `R`, which no
object operand is followed by. -/
theorem next_not_R {Q : ByteArray} {rest : List Tok} (hs : ∀ t ∈ rest, TokSpelled t)
    (hR : ∀ u ∈ rest.head?, leadR u = false) : at? (Q ++ renderL rest) Q.size ≠ 82 := by
  cases rest with
  | nil =>
    simp only [renderL_nil, ByteArray.append_empty]
    rw [at?_ge Q Q.size (Nat.le_refl _)]; decide
  | cons u rest' =>
    obtain ⟨c, cs, hcs, -, -, -, hr⟩ := head_spell u (hs u (by simp))
    have e : Q ++ renderL (u :: rest') = Q ++ spell u ++ ⟨#[10]⟩ ++ renderL rest' := by
      simp only [renderL_cons, ByteArray.append_assoc]
    rw [e, at_spell_head hcs]
    intro h82
    have := (hr h82).1
    rw [hR u (by simp)] at this
    exact absurd this (by simp)

theorem step_obj {P : ByteArray} {o : Obj} {rest : List Tok} (ho : ValSpelled o)
    (hb : readByObj o = true) (hs : ∀ t ∈ rest, TokSpelled t)
    (hR : ∀ u ∈ rest.head?, leadR u = false) {q : Nat}
    (hq : skipWs (P ++ spell (.val o) ++ ⟨#[10]⟩ ++ renderL rest) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val o) ++ ⟨#[10]⟩ ++ renderL rest) { pos := q, out } =
      .yield { pos := P.size + (spell (.val o)).size, out := out.push (.val o) } := by
  obtain ⟨c, cs, hcs, hnum, hobj, hw, hc⟩ := obj_head o ho.1 hb
  have hcs' : octets (spell (.val o)) = c :: cs := hcs
  have hhead := at_spell_head (Q := P) (R := renderL rest) hcs'
  have hfix : skipWs (P ++ spell (.val o) ++ ⟨#[10]⟩ ++ renderL rest) P.size = P.size :=
    skipWs_fixed_point (by rw [hhead]; exact hw) (by rw [hhead]; exact hc)
  have hstop : ObjReader.Stop (P ++ spell (.val o) ++ ⟨#[10]⟩ ++ renderL rest)
      (P.size + o.render.size) := by
    refine ⟨?_, ?_, ?_⟩
    · show EndByte (at? (P ++ spell (.val o) ++ ⟨#[10]⟩ ++ renderL rest) (P.size + (spell (.val o)).size))
      rw [nl_at]; exact Or.inr (Or.inl rfl)
    · show at? _ (skipWs _ (P.size + (spell (.val o)).size)) ≠ 82
      rw [skip_after hs]
      have := next_not_R (Q := P ++ spell (.val o) ++ ⟨#[10]⟩) hs hR
      have hq' : (P ++ spell (.val o) ++ ⟨#[10]⟩).size = P.size + (spell (.val o)).size + 1 := by
        simp [ByteArray.size_append, nl_size]
      rwa [hq'] at this
    · exact tryRef_after (S := spell (.val o)) hs
  have hpv := parseVal_render_span_exact o ho.1 (span_tok P (spell (.val o)) (renderL rest)) hstop hfix
  have hsz : ¬ (P ++ spell (.val o) ++ ⟨#[10]⟩ ++ renderL rest).size ≤ P.size := by
    rw [size_tok]; omega
  have hpos : P.size < P.size + o.render.size := by
    have := congrArg List.length hcs
    simp at this
    omega
  unfold step
  simp only [hq, hsz, ↓reduceIte, hhead, hnum, hobj, Bool.false_eq_true, hpv, hpos]
  rfl


/-- **One spelled token read**: from where the reader stands before it, a
step reads exactly the token and stops at its line feed. -/
theorem step_tok {P : ByteArray} {t : Tok} {rest : List Tok} (hs : Spelled (t :: rest)) {q : Nat}
    (hq : skipWs (P ++ spell t ++ ⟨#[10]⟩ ++ renderL rest) q = P.size) (out : Array Tok) :
    step (P ++ spell t ++ ⟨#[10]⟩ ++ renderL rest) { pos := q, out } =
      .yield { pos := P.size + (spell t).size, out := out.push t } := by
  obtain ⟨ht, hR, hrest⟩ := hs
  cases t with
  | inline _ _ => exact absurd ht (by simp [TokSpelled])
  | op n => exact step_op ht hq out
  | val o =>
    have ho : ValSpelled o := ht
    have hall := spelled_all hrest
    have hro := ho.1
    cases hro with
    | null => exact step_null hq out
    | bool v => exact step_bool v hq out
    | int n => exact step_int n hq out
    | real hr => exact step_real _ hr hq out
    | str hsr => exact step_obj ho rfl hall (hR _ rfl rfl) hq out
    | name hn => exact step_obj ho rfl hall (hR _ rfl rfl) hq out
    | arr hx => exact step_obj ho rfl hall (hR _ rfl rfl) hq out
    | dict hk hv => exact step_obj ho rfl hall (hR _ rfl rfl) hq out
    | ref n g => exact absurd rfl (ho.2 n g)

theorem renderL_size (ts : List Tok) : ts.length ≤ (renderL ts).size := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [renderL_cons, ByteArray.size_append, nl_size, List.length_cons]
    omega

/-- **The reading of spelled tokens runs to the end** (progress-indexed): from
where the reader stands before them, one step per token and one to stop,
leaving every token read in order. -/
theorem scan_stops (P : ByteArray) (rest : List Tok) (hs : Spelled rest) (q : Nat)
    (hq : skipWs (P ++ renderL rest) q = P.size) (out : Array Tok) :
    Loop.Stops (fun s => pure (step (P ++ renderL rest) s)) { pos := q, out } (rest.length + 1)
      { pos := (P ++ renderL rest).size, out := out ++ rest.toArray } := by
  induction rest generalizing P q out with
  | nil =>
    apply Loop.Stops.done
    simp only [renderL_nil, ByteArray.append_empty] at hq ⊢
    show step P { pos := q, out } = _
    unfold step
    simp [hq]
  | cons t rest' ih =>
    have e : P ++ renderL (t :: rest') = P ++ spell t ++ ⟨#[10]⟩ ++ renderL rest' := by
      simp only [renderL_cons, ByteArray.append_assoc]
    rw [e] at hq ⊢
    have hstep := step_tok hs hq out
    have hall := spelled_all hs.2.2
    have hskip := skip_after (P := P) (S := spell t) hall
    have e' : P ++ spell t ++ ⟨#[10]⟩ ++ renderL rest' = (P ++ spell t ++ ⟨#[10]⟩) ++ renderL rest' := rfl
    have hsz : (P ++ spell t ++ ⟨#[10]⟩).size = P.size + (spell t).size + 1 := by
      simp [ByteArray.size_append, nl_size]
    have hih := ih (P ++ spell t ++ ⟨#[10]⟩) hs.2.2 (P.size + (spell t).size)
      (by rw [hsz]; exact hskip) (out.push t)
    have hh := Loop.Stops.yield (step := fun s => pure (step (P ++ spell t ++ ⟨#[10]⟩ ++ renderL rest') s))
      (a := { pos := q, out }) (b := { pos := P.size + (spell t).size, out := out.push t })
      (by simp only [Id.run, pure]; exact hstep) hih
    have hout : out.push t ++ rest'.toArray = out ++ (t :: rest').toArray := by
      apply Array.ext'; simp
    rw [hout] at hh
    simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh


/-- **The tokenizer reads back what its writer spells** (`_exact`): tokens
the writer spells (`Spelled`) — operands the object writer spells, not
references; operators of regular characters that no operand starts — come
back from their spelling, in order, whole. -/
public theorem scan_render_exact (toks : Array Tok) (h : Spelled toks.toList) :
    scan (render toks) = toks := by
  rw [render_eq toks h]
  unfold scan
  have hall := spelled_all h
  have hh := renderL_head (Q := ByteArray.empty) hall
  simp only [ByteArray.empty_append, ByteArray.size_empty] at hh
  have h0 : skipWs (ByteArray.empty ++ renderL toks.toList) 0 = ByteArray.empty.size := by
    simp only [ByteArray.empty_append, ByteArray.size_empty]
    rcases hh with hz | hz
    · exact skipWs_fixed_point (by rw [hz]; rfl) (by rw [hz]; decide)
    · exact skipWs_fixed_point hz.1 hz.2.1
  have hst := scan_stops ByteArray.empty toks.toList h 0 h0 #[]
  simp only [ByteArray.empty_append] at hst
  rw [Loop.forIn_range_stops_exact hst ((renderL toks.toList).size + 2)
    (by have := renderL_size toks.toList; omega)]
  simp

end LeanTex.Core.PdfContentLex
