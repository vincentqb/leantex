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

/-! The content tokenizer reads back the tokens its writer spells. -/

namespace LeanTex.Core.PdfContentLex

open LeanTex.Core.PdfLex LeanTex.Core.PdfRead

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

/-- An operator the writer spells: regular ASCII, the first no number's, neither a tokenizer keyword
nor the reference marker. -/
public structure OpSpelled (n : String) : Prop where
  ne : n.toList ≠ []
  ascii : ∀ c ∈ n.toList, c.toNat < 128
  reg : ∀ c ∈ n.toList, regular c.toNat = true
  lead : ∀ c, n.toList.head? = some c → numByte c.toNat = false
  word : n ≠ "true" ∧ n ≠ "false" ∧ n ≠ "null" ∧ n ≠ "BI" ∧ n ≠ "R"

/-- An operand the writer spells: a representable object other than a reference (§7.8.2). -/
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

/-- A token the writer spells: an operand or an operator, never an inline image. -/
@[expose] public def TokSpelled : Tok → Prop
  | .val o => ValSpelled o
  | .op n => OpSpelled n
  | .inline _ _ => False

/-- Tokens the writer spells, with no object-read operand followed by an operator spelled with a leading `R`. -/
public def Spelled : List Tok → Prop
  | [] => True
  | t :: rest => TokSpelled t ∧
    (∀ o, t = .val o → readByObj o = true → ∀ u ∈ rest.head?, leadR u = false) ∧ Spelled rest

/-- A token's bytes. -/
@[expose] public def spell : Tok → ByteArray
  | .val o => o.render
  | .op n => n.toUTF8
  | .inline d data => Tok.renderInto ByteArray.empty (.inline d data)

/-- A run of regular ASCII characters that no number starts: what the
tokenizer reads as a word at a token's start. -/
structure Word (w : String) : Prop where
  ne : w.toList ≠ []
  ascii : ∀ c ∈ w.toList, c.toNat < 128
  reg : ∀ c ∈ w.toList, regular c.toNat = true
  lead : ∀ c, w.toList.head? = some c → numByte c.toNat = false

/-- A byte that ends a token: the stream's end, or white space. -/
def TermByte (c : Nat) : Prop := c = 256 ∨ isWs c = true

/-- What follows a token: its byte, after the last token only when `trail`. -/
@[expose] public def sepOf (trail : Bool) (w : UInt8) : List (Tok × UInt8) → ByteArray
  | [] => if trail then ⟨#[w]⟩ else .empty
  | _ :: _ => ⟨#[w]⟩

/-- `renderSep trail` of the tokens, appended to `acc`. -/
@[expose] public def renderSepInto (trail : Bool) (acc : ByteArray) : List (Tok × UInt8) → ByteArray
  | [] => acc
  | (t, w) :: rest => renderSepInto trail (acc ++ spell t ++ sepOf trail w rest) rest

/-- Tokens each spelled and followed by its byte, the last token's byte only when `trail`. -/
@[expose] public def renderSep (trail : Bool) (ts : List (Tok × UInt8)) : ByteArray :=
  renderSepInto trail .empty ts

theorem renderSepInto_acc (trail : Bool) (acc : ByteArray) (ts : List (Tok × UInt8)) :
    renderSepInto trail acc ts = acc ++ renderSep trail ts := by
  induction ts generalizing acc with
  | nil => simp [renderSepInto, renderSep]
  | cons p rest ih =>
    obtain ⟨t, w⟩ := p
    simp only [renderSep, renderSepInto]
    rw [ih, ih (ByteArray.empty ++ spell t ++ sepOf trail w rest)]
    simp [ByteArray.append_assoc]

public theorem renderSep_nil (trail : Bool) : renderSep trail [] = .empty := rfl

public theorem renderSep_cons (trail : Bool) (t : Tok) (w : UInt8) (rest : List (Tok × UInt8)) :
    renderSep trail ((t, w) :: rest) = spell t ++ sepOf trail w rest ++ renderSep trail rest := by
  rw [renderSep, renderSepInto, renderSepInto_acc, ByteArray.empty_append]

public theorem sepOf_true (w : UInt8) (rest : List (Tok × UInt8)) : sepOf true w rest = ⟨#[w]⟩ := by
  cases rest <;> rfl

public theorem renderSep_true : ∀ (ts : List (Tok × UInt8)) (h : ts ≠ []),
    renderSep true ts = renderSep false ts ++ ⟨#[(ts.getLast h).2]⟩
  | [(t, w)], _ => by simp [renderSep_cons, renderSep_nil, sepOf]
  | (t, w) :: u :: rest, _ => by
    rw [renderSep_cons true t w, renderSep_cons false t w, renderSep_true (u :: rest) (by simp),
      List.getLast_cons_cons]
    simp only [sepOf, ByteArray.append_assoc]

theorem renderSep_cons_after (Q : ByteArray) (trail : Bool) (t : Tok) (w : UInt8)
    (rest : List (Tok × UInt8)) :
    Q ++ renderSep trail ((t, w) :: rest) = Q ++ spell t ++ (sepOf trail w rest ++ renderSep trail rest) := by
  simp only [renderSep_cons, ByteArray.append_assoc]

theorem renderInto_spell (acc : ByteArray) (t : Tok) (ht : TokSpelled t) :
    t.renderInto acc = acc ++ spell t := by
  cases t with
  | val o => simp [Tok.renderInto, spell]
  | op n => simp [Tok.renderInto, spell]
  | inline d data => exact absurd ht (by simp [TokSpelled])

theorem foldl_render (acc : ByteArray) (ts : List Tok) (h : ∀ t ∈ ts, TokSpelled t) :
    ts.foldl (fun acc t => (t.renderInto acc).push 10) acc = acc ++ renderSep true (ts.map (·, 10)) := by
  induction ts generalizing acc with
  | nil => simp [renderSep_nil]
  | cons t ts ih =>
    simp only [List.foldl_cons, List.map_cons, renderSep_cons, sepOf_true]
    rw [ih _ (fun u hu => h u (by simp [hu])), renderInto_spell acc t (h t (by simp))]
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

theorem render_eq (toks : Array Tok) (h : ∀ t ∈ toks.toList, TokSpelled t) :
    render toks = renderSep true (toks.toList.map (·, 10)) := by
  unfold render
  rw [← Array.foldl_toList, foldl_render ByteArray.empty toks.toList h]
  simp

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

theorem regular_ws {c : Nat} (h : isWs c = true) : regular c = false := by
  simp [regular, h]

theorem objStart_not_regular {c : Nat} (h : regular c = true) : objStart c = false := by
  simp only [regular, isWs, isDelim, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_iff_ne, ne_eq] at h
  simp only [objStart, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  omega

theorem OpSpelled.word' {n : String} (h : OpSpelled n) : Word n := ⟨h.ne, h.ascii, h.reg, h.lead⟩

theorem word_true : Word "true" := ⟨by decide, by decide, by decide, by decide⟩
theorem word_false : Word "false" := ⟨by decide, by decide, by decide, by decide⟩
theorem word_null : Word "null" := ⟨by decide, by decide, by decide, by decide⟩

theorem numberObj_int (n : Int) : numberObj (toString n) = some (.int n) := by
  unfold numberObj
  rw [Number.int_noDot, Number.int_toString_id]
  rfl

theorem numberObj_real (r : String) (h : Obj.RealSpelling r) : numberObj r = some (.real r) := by
  have : r.contains '.' = true := by
    rw [String.contains_char_eq]
    exact decide_eq_true h.1
  simp [numberObj, this]

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

theorem toString_ofNat_int (k : Nat) : toString (Int.ofNat k) = toString k := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  simp

theorem digit_not_numByte_false {c : Nat} (h : 48 ≤ c ∧ c ≤ 57) : numByte c = true := by
  simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

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

theorem TermByte.not_regular {c : Nat} (h : TermByte c) : regular c = false := by
  rcases h with rfl | h
  · rfl
  · exact regular_ws h

theorem TermByte.not_number {c : Nat} (h : TermByte c) : numByte c = false := by
  rcases h with rfl | h
  · rfl
  · simp only [isWs, Bool.or_eq_true, beq_iff_eq] at h
    simp only [numByte, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]
    omega

theorem TermByte.end_byte {c : Nat} (h : TermByte c) : EndByte c := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem after_at (P S R : ByteArray) : at? (P ++ S ++ R) (P.size + S.size) = at? R 0 := by
  have h := at?_append_right (P ++ S) R 0
  simpa [ByteArray.size_append] using h

theorem single_size (w : UInt8) : (⟨#[w]⟩ : ByteArray).size = 1 := rfl

theorem at_single (w : UInt8) (R : ByteArray) : at? (⟨#[w]⟩ ++ R) 0 = w.toNat := by
  have h1 : (0 : Nat) < (⟨#[w]⟩ : ByteArray).size := Nat.zero_lt_one
  rw [at?_append_left _ _ _ h1]
  rfl

theorem sepOf_cases (trail : Bool) (w : UInt8) (rest : List (Tok × UInt8)) :
    sepOf trail w rest = ⟨#[w]⟩ ∨ (sepOf trail w rest = .empty ∧ rest = []) := by
  cases rest with
  | nil => cases trail <;> simp [sepOf]
  | cons _ _ => exact Or.inl rfl

theorem sep_term (trail : Bool) (w : UInt8) (hw : isWs w.toNat = true) (rest : List (Tok × UInt8)) :
    TermByte (at? (sepOf trail w rest ++ renderSep trail rest) 0) := by
  rcases sepOf_cases trail w rest with he | ⟨he, rfl⟩
  · right
    rw [he, at_single]
    exact hw
  · left
    simp only [he, renderSep_nil, ByteArray.empty_append]
    exact at?_ge _ 0 (by simp)

theorem span_tok (P S R : ByteArray) : Span (P ++ S ++ R) P.size (octets S) := by
  have := Span.of_bytes P S R
  simpa [octets] using this

theorem size_tok (P S R : ByteArray) : (P ++ S ++ R).size = P.size + S.size + R.size := by
  simp [ByteArray.size_append]

theorem word_read {P R : ByteArray} {w : String} (hw : Word w) (hT : TermByte (at? R 0)) :
    let B := P ++ w.toUTF8 ++ R
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
    show regular (at? (P ++ w.toUTF8 ++ R) (P.size + w.toUTF8.size)) = false
    rw [after_at]
    exact hT.not_regular
  have hrun := runEnd_exact hspan (fun d hd => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact hw.reg e he) hend
  have hname := asciiAt_exact hspan
  rw [ascii_name, List.length_map, ← hlen] at hname
  rw [List.length_map, ← hlen] at hrun
  have hpos1 : w.toUTF8.size ≥ 1 := by rw [hlen, hcs]; simp
  refine ⟨by show ¬ (P ++ w.toUTF8 ++ R).size ≤ P.size; rw [size_tok]; omega,
    by rw [hhead]; exact hw.lead c (by simp [hcs]), by rw [hhead]; exact objStart_not_regular hreg,
    by rw [hhead]; exact hreg, hrun, hname, ?_⟩
  have : w.toList.length ≥ 1 := by rw [hcs]; simp
  omega

theorem step_op {P R : ByteArray} {n : String} (hn : OpSpelled n) (hT : TermByte (at? R 0)) {q : Nat}
    (hq : skipWs (P ++ n.toUTF8 ++ R) q = P.size) (out : Array Tok) :
    step (P ++ n.toUTF8 ++ R) { pos := q, out } =
      .yield { pos := P.size + n.toUTF8.size, out := out.push (.op n) } := by
  obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, hpos⟩ := word_read (P := P) (R := R) hn.word' hT
  unfold step
  simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname]
  obtain ⟨h1, h2, h3, h4, _⟩ := hn.word
  simp only [beq_iff_eq, h1, h2, h3, h4, ↓reduceIte]
  congr
  omega

theorem step_bool {P R : ByteArray} (v : Bool) (hT : TermByte (at? R 0)) {q : Nat}
    (hq : skipWs (P ++ spell (.val (.bool v)) ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val (.bool v)) ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val (.bool v))).size, out := out.push (.val (.bool v)) } := by
  cases v with
  | true =>
    have hs : spell (.val (.bool true)) = "true".toUTF8 := by simp [spell, Obj.render, Obj.renderInto]
    rw [hs] at hq ⊢
    obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, -⟩ := word_read (P := P) (R := R) word_true hT
    unfold step
    simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname, beq_self_eq_true]
  | false =>
    have hs : spell (.val (.bool false)) = "false".toUTF8 := by simp [spell, Obj.render, Obj.renderInto]
    rw [hs] at hq ⊢
    obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, -⟩ := word_read (P := P) (R := R) word_false hT
    unfold step
    simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname]
    simp

theorem step_null {P R : ByteArray} (hT : TermByte (at? R 0)) {q : Nat}
    (hq : skipWs (P ++ spell (.val .null) ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val .null) ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val .null)).size, out := out.push (.val .null) } := by
  have hs : spell (.val .null) = "null".toUTF8 := by simp [spell, Obj.render, Obj.renderInto]
  rw [hs] at hq ⊢
  obtain ⟨hsz, hnum, hobj, hreg, hrun, hname, -⟩ := word_read (P := P) (R := R) word_null hT
  unfold step
  simp only [hq, hsz, ↓reduceIte, hnum, hobj, hreg, Bool.false_eq_true, hrun, hname]
  simp

theorem step_number {P R : ByteArray} {raw : String} {o : Obj}
    (hc : ∀ c ∈ raw.toList, numByte c.toNat = true) (hne : raw.toList ≠ [])
    (ho : numberObj raw = some o) (hT : TermByte (at? R 0)) {q : Nat}
    (hq : skipWs (P ++ raw.toUTF8 ++ R) q = P.size) (out : Array Tok) :
    step (P ++ raw.toUTF8 ++ R) { pos := q, out } =
      .yield { pos := P.size + raw.toUTF8.size, out := out.push (.val o) } := by
  have hoct := numeric_octets raw hc
  have hspan := span_tok P raw.toUTF8 R
  rw [hoct] at hspan
  have hlen : raw.toUTF8.size = raw.toList.length := numeric_size raw hc
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, raw.toList = c :: cs := by
    cases h : raw.toList with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hhead : at? (P ++ raw.toUTF8 ++ R) P.size = c.toNat := by
    have hs := hspan
    rw [hcs, List.map_cons] at hs
    exact hs.head
  have hnum : numByte c.toNat = true := hc c (by simp [hcs])
  have hend : numByte (at? (P ++ raw.toUTF8 ++ R) (P.size + raw.toList.length)) = false := by
    rw [← hlen, after_at]
    exact hT.not_number
  have hscan := scanNumber_exact hspan hc hend
  have hpos1 : raw.toUTF8.size ≥ 1 := by rw [hlen, hcs]; simp
  have hsz : ¬ (P ++ raw.toUTF8 ++ R).size ≤ P.size := by
    rw [size_tok]; omega
  unfold step
  simp only [hq, hsz, ↓reduceIte, hhead, hnum, hscan, String.ofList_toList, ho, hlen]
  congr
  omega

theorem step_int {P R : ByteArray} (n : Int) (hT : TermByte (at? R 0)) {q : Nat}
    (hq : skipWs (P ++ spell (.val (.int n)) ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val (.int n)) ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val (.int n))).size, out := out.push (.val (.int n)) } := by
  have hs : spell (.val (.int n)) = (toString n).toUTF8 := by
    simp [spell, Obj.render, Obj.renderInto]
  rw [hs] at hq ⊢
  exact step_number (int_chars_num n) (Number.int_nonempty n) (numberObj_int n) hT hq out

theorem step_real {P R : ByteArray} (r : String) (hr : Obj.RealSpelling r) (hT : TermByte (at? R 0)) {q : Nat}
    (hq : skipWs (P ++ spell (.val (.real r)) ++ R) q = P.size) (out : Array Tok) :
    step (P ++ spell (.val (.real r)) ++ R) { pos := q, out } =
      .yield { pos := P.size + (spell (.val (.real r))).size, out := out.push (.val (.real r)) } := by
  have hs : spell (.val (.real r)) = r.toUTF8 := by
    simp [spell, Obj.render, Obj.renderInto]
  rw [hs] at hq ⊢
  have hne : r.toList ≠ [] := by
    intro h; have := hr.1; rw [h] at this; simp at this
  exact step_number hr.2 hne (numberObj_real r hr) hT hq out

theorem renderSep_head {Q : ByteArray} {trail : Bool} {rest : List (Tok × UInt8)}
    (hs : ∀ t ∈ rest, TokSpelled t.1) :
    (at? (Q ++ renderSep trail rest) Q.size = 256) ∨
      (isWs (at? (Q ++ renderSep trail rest) Q.size) = false ∧ at? (Q ++ renderSep trail rest) Q.size ≠ 37 ∧
        at? (Q ++ renderSep trail rest) Q.size < 256 ∧
        (at? (Q ++ renderSep trail rest) Q.size = 82 →
          regular (at? (Q ++ renderSep trail rest) (Q.size + 1)) = true)) := by
  cases rest with
  | nil =>
    left
    simp only [renderSep_nil, ByteArray.append_empty]
    exact at?_ge Q Q.size (Nat.le_refl _)
  | cons p rest' =>
    right
    obtain ⟨u, w⟩ := p
    obtain ⟨c, cs, hcs, hw, hc, hlt, hr⟩ := head_spell u (hs (u, w) (by simp))
    have hspan := span_tok Q (spell u) (sepOf trail w rest' ++ renderSep trail rest')
    rw [hcs] at hspan
    rw [renderSep_cons_after, hspan.head]
    refine ⟨hw, hc, hlt, fun h82 => ?_⟩
    obtain ⟨_, d, ds, hd, hreg⟩ := hr h82
    rw [hd] at hspan
    rw [hspan.tail.head]
    exact hreg

theorem skip_after {P S : ByteArray} {trail : Bool} {w : UInt8} (hw : isWs w.toNat = true)
    {rest : List (Tok × UInt8)} (hs : ∀ t ∈ rest, TokSpelled t.1) :
    skipWs (P ++ S ++ sepOf trail w rest ++ renderSep trail rest) (P.size + S.size) =
      (P ++ S ++ sepOf trail w rest).size := by
  rcases sepOf_cases trail w rest with he | ⟨he, rfl⟩
  · rw [he]
    have hh := renderSep_head (trail := trail) (Q := P ++ S ++ ⟨#[w]⟩) hs
    have hq : (P ++ S ++ ⟨#[w]⟩).size = P.size + S.size + 1 := by
      simp [ByteArray.size_append, single_size]
    rw [hq] at hh ⊢
    have hat : at? (P ++ S ++ ⟨#[w]⟩ ++ renderSep trail rest) (P.size + S.size) = w.toNat := by
      have e : P ++ S ++ ⟨#[w]⟩ ++ renderSep trail rest = P ++ S ++ (⟨#[w]⟩ ++ renderSep trail rest) := by
        simp only [ByteArray.append_assoc]
      rw [e, after_at, at_single]
    apply skipWs_whitespace_exact
    · rw [hat]; exact hw
    · rcases hh with h | h
      · rw [h]; rfl
      · exact h.1
    · rcases hh with h | h
      · rw [h]; decide
      · exact h.2.1
    · simp only [ByteArray.size_append, single_size]; omega
  · simp only [he, renderSep_nil, ByteArray.append_empty]
    rw [ByteArray.size_append]
    have hend : at? (P ++ S) (P.size + S.size) = 256 := at?_ge _ _ (by simp [ByteArray.size_append])
    exact skipWs_fixed_point (by rw [hend]; rfl) (by rw [hend]; decide)

theorem tryRef_after {P S : ByteArray} {trail : Bool} {w : UInt8} (hw : isWs w.toNat = true)
    {rest : List (Tok × UInt8)} (hs : ∀ t ∈ rest, TokSpelled t.1) (hws : ∀ t ∈ rest, isWs t.2.toNat = true) :
    tryRef (P ++ S ++ sepOf trail w rest ++ renderSep trail rest) (P.size + S.size) = none := by
  apply tryRef_none_of
  intro gen j hp h82
  rw [skip_after hw hs] at hp
  cases rest with
  | nil =>
    have h256 :
        at? (P ++ S ++ sepOf trail w [] ++ renderSep trail []) (P ++ S ++ sepOf trail w []).size = 256 := by
      apply at?_ge; simp [renderSep_nil, ByteArray.size_append]
    rw [parseUInt_none (by rw [h256]; omega)] at hp
    exact absurd hp (by simp)
  | cons p rest' =>
    obtain ⟨u, w'⟩ := p
    have hsu : TokSpelled u := hs (u, w') (by simp)
    have hw' : isWs w'.toNat = true := hws (u, w') (by simp)
    have hrest : ∀ t ∈ rest', TokSpelled t.1 := fun t ht => hs t (by simp [ht])
    have e : P ++ S ++ sepOf trail w ((u, w') :: rest') ++ renderSep trail ((u, w') :: rest') =
        (P ++ S ++ sepOf trail w ((u, w') :: rest')) ++
          (spell u ++ (sepOf trail w' rest' ++ renderSep trail rest')) := by
      simp only [renderSep_cons, ByteArray.append_assoc]
    rw [e] at hp h82 ⊢
    generalize P ++ S ++ sepOf trail w ((u, w') :: rest') = Q at hp h82 ⊢
    obtain ⟨c, cs, hcs, hcw, hc, hlt, hr⟩ := head_spell u hsu
    have hspan0 := span_tok Q (spell u) (sepOf trail w' rest' ++ renderSep trail rest')
    simp only [ByteArray.append_assoc] at hspan0
    have hhead : at? (Q ++ (spell u ++ (sepOf trail w' rest' ++ renderSep trail rest'))) Q.size = c := by
      rw [hcs] at hspan0; exact hspan0.head
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
        have hspan := span_tok Q (spell (.val o)) (sepOf trail w' rest' ++ renderSep trail rest')
        simp only [ByteArray.append_assoc] at hspan
        have hterm : TermByte (at? (Q ++ (spell (.val o) ++ (sepOf trail w' rest' ++ renderSep trail rest')))
            (Q.size + (spell (.val o)).size)) := by
          have h := after_at Q (spell (.val o)) (sepOf trail w' rest' ++ renderSep trail rest')
          simp only [ByteArray.append_assoc] at h
          rw [h]; exact sep_term trail w' hw' rest'
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
            have hpn := parse_nat hspan (by rw [← hsz]; exact hterm.end_byte)
            rw [hpn] at hp
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨-, rfl⟩ := hp
            have hsk := skip_after (P := Q) (S := spell (.val (.int (Int.ofNat k)))) (trail := trail) hw' hrest
            simp only [ByteArray.append_assoc] at hsk
            rw [← hsz, hsk] at h82 ⊢
            have hh := renderSep_head (trail := trail)
              (Q := Q ++ spell (.val (.int (Int.ofNat k))) ++ sepOf trail w' rest') hrest
            simp only [ByteArray.append_assoc] at hh
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
          have hat : at? (Q ++ (spell (.val (.real r)) ++ (sepOf trail w' rest' ++ renderSep trail rest')))
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

theorem next_not_R {Q : ByteArray} {trail : Bool} {rest : List (Tok × UInt8)} (hs : ∀ t ∈ rest, TokSpelled t.1)
    (hR : ∀ u ∈ rest.head?, leadR u.1 = false) : at? (Q ++ renderSep trail rest) Q.size ≠ 82 := by
  cases rest with
  | nil =>
    simp only [renderSep_nil, ByteArray.append_empty]
    rw [at?_ge Q Q.size (Nat.le_refl _)]; decide
  | cons p rest' =>
    obtain ⟨u, w⟩ := p
    obtain ⟨c, cs, hcs, -, -, -, hr⟩ := head_spell u (hs (u, w) (by simp))
    have hspan := span_tok Q (spell u) (sepOf trail w rest' ++ renderSep trail rest')
    rw [hcs] at hspan
    rw [renderSep_cons_after, hspan.head]
    intro h82
    have := (hr h82).1
    rw [hR (u, w) (by simp)] at this
    exact absurd this (by simp)

theorem step_obj {P : ByteArray} {o : Obj} {trail : Bool} {w : UInt8} {rest : List (Tok × UInt8)}
    (ho : ValSpelled o) (hb : readByObj o = true) (hw : isWs w.toNat = true) (hs : ∀ t ∈ rest, TokSpelled t.1)
    (hws : ∀ t ∈ rest, isWs t.2.toNat = true) (hR : ∀ u ∈ rest.head?, leadR u.1 = false) {q : Nat}
    (hq : skipWs (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest) q = P.size)
    (out : Array Tok) :
    step (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest) { pos := q, out } =
      .yield { pos := P.size + (spell (.val o)).size, out := out.push (.val o) } := by
  obtain ⟨c, cs, hcs, hnum, hobj, hcw, hc⟩ := obj_head o ho.1 hb
  have hcs' : octets (spell (.val o)) = c :: cs := hcs
  have hspan := span_tok P (spell (.val o)) (sepOf trail w rest ++ renderSep trail rest)
  rw [← ByteArray.append_assoc] at hspan
  have hspan0 := hspan
  rw [hcs'] at hspan0
  have hhead : at? (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest) P.size = c :=
    hspan0.head
  have hfix : skipWs (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest) P.size = P.size :=
    skipWs_fixed_point (by rw [hhead]; exact hcw) (by rw [hhead]; exact hc)
  have hstop : ObjReader.Stop (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest)
      (P.size + o.render.size) := by
    refine ⟨?_, ?_, ?_⟩
    · show EndByte (at? (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest)
        (P.size + (spell (.val o)).size))
      have h := after_at P (spell (.val o)) (sepOf trail w rest ++ renderSep trail rest)
      simp only [ByteArray.append_assoc] at h ⊢
      rw [h]; exact (sep_term trail w hw rest).end_byte
    · show at? _ (skipWs _ (P.size + (spell (.val o)).size)) ≠ 82
      rw [skip_after hw hs]
      exact next_not_R hs hR
    · exact tryRef_after (S := spell (.val o)) hw hs hws
  have hpv := parseVal_render_span_exact o ho.1 hspan hstop hfix
  have hlen1 : (spell (.val o)).size = cs.length + 1 := by
    have := congrArg List.length hcs'
    simpa [octets] using this
  have hsz : ¬ (P ++ spell (.val o) ++ sepOf trail w rest ++ renderSep trail rest).size ≤ P.size := by
    simp only [ByteArray.size_append]
    omega
  have hpos : P.size < P.size + o.render.size := by
    have := congrArg List.length hcs
    simp at this
    omega
  unfold step
  simp only [hq, hsz, ↓reduceIte, hhead, hnum, hobj, Bool.false_eq_true, hpv, hpos]
  rfl

theorem step_tok {P : ByteArray} {t : Tok} {trail : Bool} {w : UInt8} {rest : List (Tok × UInt8)}
    (hs : Spelled (t :: rest.map (·.1))) (hw : isWs w.toNat = true) (hws : ∀ u ∈ rest, isWs u.2.toNat = true)
    {q : Nat} (hq : skipWs (P ++ spell t ++ sepOf trail w rest ++ renderSep trail rest) q = P.size)
    (out : Array Tok) :
    step (P ++ spell t ++ sepOf trail w rest ++ renderSep trail rest) { pos := q, out } =
      .yield { pos := P.size + (spell t).size, out := out.push t } := by
  obtain ⟨ht, hR, hrest⟩ := hs
  have hall : ∀ u ∈ rest, TokSpelled u.1 := fun u hu => spelled_all hrest u.1 (List.mem_map_of_mem hu)
  have hT : TermByte (at? (sepOf trail w rest ++ renderSep trail rest) 0) := sep_term trail w hw rest
  have e : P ++ spell t ++ sepOf trail w rest ++ renderSep trail rest =
      P ++ spell t ++ (sepOf trail w rest ++ renderSep trail rest) := by
    simp only [ByteArray.append_assoc]
  cases t with
  | inline _ _ => exact absurd ht (by simp [TokSpelled])
  | op n =>
    rw [e] at hq ⊢
    exact step_op ht hT hq out
  | val o =>
    have ho : ValSpelled o := ht
    have hro := ho.1
    have hR' : readByObj o = true → ∀ u ∈ rest.head?, leadR u.1 = false := by
      intro hb u hu
      cases rest with
      | nil => simp at hu
      | cons r rs =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hu
        subst hu
        exact hR o rfl hb r.1 (by simp)
    cases hro with
    | null => rw [e] at hq ⊢; exact step_null hT hq out
    | bool v => rw [e] at hq ⊢; exact step_bool v hT hq out
    | int n => rw [e] at hq ⊢; exact step_int n hT hq out
    | real hr => rw [e] at hq ⊢; exact step_real _ hr hT hq out
    | str hsr => exact step_obj ho rfl hw hall hws (hR' rfl) hq out
    | name hn => exact step_obj ho rfl hw hall hws (hR' rfl) hq out
    | arr hx => exact step_obj ho rfl hw hall hws (hR' rfl) hq out
    | dict hk hv => exact step_obj ho rfl hw hall hws (hR' rfl) hq out
    | ref n g => exact absurd rfl (ho.2 n g)

theorem scan_stops (P : ByteArray) (trail : Bool) (rest : List (Tok × UInt8)) (hs : Spelled (rest.map (·.1)))
    (hws : ∀ u ∈ rest, isWs u.2.toNat = true) (q : Nat)
    (hq : skipWs (P ++ renderSep trail rest) q = P.size) (out : Array Tok) :
    Loop.Stops (fun s => pure (step (P ++ renderSep trail rest) s)) { pos := q, out } (rest.length + 1)
      { pos := (P ++ renderSep trail rest).size, out := out ++ (rest.map (·.1)).toArray } := by
  induction rest generalizing P q out with
  | nil =>
    apply Loop.Stops.done
    simp only [renderSep_nil, ByteArray.append_empty] at hq ⊢
    show step P { pos := q, out } = _
    unfold step
    simp [hq]
  | cons p rest' ih =>
    obtain ⟨t, w⟩ := p
    have hw : isWs w.toNat = true := hws (t, w) (by simp)
    have hws' : ∀ u ∈ rest', isWs u.2.toNat = true := fun u hu => hws u (by simp [hu])
    have e : P ++ renderSep trail ((t, w) :: rest') =
        P ++ spell t ++ sepOf trail w rest' ++ renderSep trail rest' := by
      simp only [renderSep_cons, ByteArray.append_assoc]
    rw [e] at hq ⊢
    have hstep := step_tok (P := P) (by simpa using hs) hw hws' hq out
    have hall : ∀ u ∈ rest', TokSpelled u.1 := fun u hu =>
      spelled_all hs.2.2 u.1 (List.mem_map_of_mem hu)
    have hskip := skip_after (P := P) (S := spell t) (trail := trail) hw hall
    have hih := ih (P ++ spell t ++ sepOf trail w rest') hs.2.2 hws' (P.size + (spell t).size)
      (by rw [hskip]) (out.push t)
    have hh := Loop.Stops.yield
      (step := fun s => pure (step (P ++ spell t ++ sepOf trail w rest' ++ renderSep trail rest') s))
      (a := { pos := q, out }) (b := { pos := P.size + (spell t).size, out := out.push t })
      (by simp only [Id.run, pure]; exact hstep) hih
    have hout : out.push t ++ (rest'.map (·.1)).toArray = out ++ (((t, w) :: rest').map (·.1)).toArray := by
      apply Array.ext'; simp
    rw [hout] at hh
    simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

theorem renderSep_size (trail : Bool) (ts : List (Tok × UInt8)) (hs : ∀ t ∈ ts, TokSpelled t.1) :
    ts.length ≤ (renderSep trail ts).size := by
  induction ts with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨t, w⟩ := p
    obtain ⟨c, cs, hcs, -⟩ := head_spell t (hs (t, w) (by simp))
    have hpos : 1 ≤ (spell t).size := by
      have := congrArg List.length hcs
      simp [octets] at this
      omega
    have := ih (fun u hu => hs u (by simp [hu]))
    simp only [renderSep_cons, ByteArray.size_append, List.length_cons]
    omega

public theorem scan_renderSep_exact (trail : Bool) (ts : List (Tok × UInt8)) (h : Spelled (ts.map (·.1)))
    (hws : ∀ t ∈ ts, isWs t.2.toNat = true) :
    scan (renderSep trail ts) = (ts.map (·.1)).toArray := by
  unfold scan
  have hall : ∀ t ∈ ts, TokSpelled t.1 := fun t ht => spelled_all h t.1 (List.mem_map_of_mem ht)
  have hh := renderSep_head (trail := trail) (Q := ByteArray.empty) hall
  simp only [ByteArray.empty_append, ByteArray.size_empty] at hh
  have h0 : skipWs (ByteArray.empty ++ renderSep trail ts) 0 = ByteArray.empty.size := by
    simp only [ByteArray.empty_append, ByteArray.size_empty]
    rcases hh with hz | hz
    · exact skipWs_fixed_point (by rw [hz]; rfl) (by rw [hz]; decide)
    · exact skipWs_fixed_point hz.1 hz.2.1
  have hst := scan_stops ByteArray.empty trail ts h hws 0 h0 #[]
  simp only [ByteArray.empty_append] at hst
  rw [Loop.forIn_range_stops_exact hst ((renderSep trail ts).size + 2)
    (by have := renderSep_size trail ts hall; omega)]
  simp

public theorem scan_render_exact (toks : Array Tok) (h : Spelled toks.toList) :
    scan (render toks) = toks := by
  rw [render_eq toks (spelled_all h),
    scan_renderSep_exact true _ (by simpa [Function.comp_def] using h)
      (fun t ht => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp ht; rfl)]
  simp [Function.comp_def]

end LeanTex.Core.PdfContentLex
