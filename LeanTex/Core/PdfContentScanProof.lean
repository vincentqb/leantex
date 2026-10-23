module

public import LeanTex.Core.PdfContentText
public import LeanTex.Core.PdfContentLexProof
import all LeanTex.Core.PdfGfxReadback
import all LeanTex.Core.PdfContent
import all LeanTex.Core.PdfContentLex
import all LeanTex.Core.PdfContentLexProof
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfObjSpelling
import LeanTex.Core.PdfLexProof
import LeanTex.Core.PdfTextProof
import all LeanTex.Core.PdfNameProof

/-! The bytes the writer spells for a text object scan back as the tokens the text reading reads. -/

namespace LeanTex.Core.PdfContent

open LeanTex.Core LeanTex.Core.Pdf LeanTex.Core.Dim LeanTex.Core.PdfGfx
open LeanTex.Core.PdfContentLex (Tok)
open LeanTex.Core.PdfRead (Obj)
open LeanTex.Core.PdfTextRead

/-! ### The writer's operands -/

/-- A number string as the operand the tokenizer reads it as. -/
@[expose] public def numObj (s : String) : Obj := (PdfContentLex.numberObj s).getD .null

/-- A number string the writer copies into a stream, spelled as the operand it reads back as. -/
@[expose] public def NumSpelled (s : String) : Prop :=
  (numObj s).render = s.toUTF8 ∧ PdfContentLex.ValSpelled (numObj s)

/-- A colour whose fill operator the writer spells as operands the tokenizer reads back: each
component string a number, each thousandth at most one. -/
@[expose] public def ColorSpelled (c : Ir.Color) : Prop :=
  match c.pdfModel with
  | some (.rgb r g b) => NumSpelled r ∧ NumSpelled g ∧ NumSpelled b
  | some (.gray v) => NumSpelled v
  | some (.cmyk cy m y k) => NumSpelled cy ∧ NumSpelled m ∧ NumSpelled y ∧ NumSpelled k
  | some (.separation _ _) => True
  | none =>
    match c.cmyk with
    | some (cy, m, y, k) => cy ≤ 1000 ∧ m ≤ 1000 ∧ y ≤ 1000 ∧ k ≤ 1000
    | none => True

mutual

/-- The text operators' colours and marked-content tags hold the writer's spellings. -/
@[expose] public def TextOp.Spelled : TextOp → Prop
  | .color c => ColorSpelled c
  | .marked (.content s _ _) body => Obj.NameSpelling s ∧ TextOp.SpelledList body.toList
  | .marked _ body => TextOp.SpelledList body.toList
  | .scale _ | .move _ _ | .font _ _ | .show _ => True

@[expose] public def TextOp.SpelledList : List TextOp → Prop
  | [] => True
  | o :: rest => TextOp.Spelled o ∧ TextOp.SpelledList rest

end

/-- The scaling operand the writer spells: tenths of a percent. -/
def scaleObj (p : Int) : Obj := .real s!"{p / 10}.{p % 10}"

/-- A colour's fill operators as the writer spells them. -/
def colorToks (c : Ir.Color) : List (List Obj × String) :=
  match c.pdfModel with
  | some (.rgb r g b) => [([numObj r, numObj g, numObj b], "rg")]
  | some (.gray v) => [([numObj v], "g")]
  | some (.cmyk cy m y k) => [([numObj cy, numObj m, numObj y, numObj k], "k")]
  | some (.separation i t) => [([.name i.resKey], "cs"), ([ratObj t.num t.den], "scn")]
  | none =>
    match c.cmyk with
    | some (cy, m, y, k) => [([milliObj cy, milliObj m, milliObj y, milliObj k], "k")]
    | none =>
      [([milliObj (Ir.Color.milli c.r), milliObj (Ir.Color.milli c.g),
        milliObj (Ir.Color.milli c.b)], "rg")]

/-- The writer's spelling of the operands a text reading reads past. -/
public def writerSpell : Spell where
  len := lenObj
  scale := scaleObj
  color := colorToks

/-! ### Spellings as characters -/

theorem escapeName_plain (s : String) (hne : s ≠ "") (hk : ∀ c ∈ s.toList, PdfLex.nameKeeps c = true) :
    PdfLex.escapeName s = s := by
  rw [PdfLex.escapeName_exact s hne]
  conv => rhs; rw [← String.ofList_toList (s := s)]
  congr 1
  have : ∀ l : List Char, (∀ c ∈ l, PdfLex.nameKeeps c = true) → l.flatMap PdfLex.nameChars = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons c rest ih =>
      simp only [List.flatMap_cons, PdfLex.nameChars, hl c (by simp), ↓reduceIte,
        List.singleton_append]
      rw [ih (fun d hd => hl d (by simp [hd]))]
  exact this _ hk

theorem push_space (a : ByteArray) : a.push 32 = a ++ " ".toUTF8 := by
  rw [show " ".toUTF8 = ByteArray.empty.push 32 by rw [String.toUTF8_eq_toByteArray]; rfl]
  apply ByteArray.ext
  simp

/-- Objects each rendered as its string. -/
def RendersAs : List Obj → List String → Prop
  | [], [] => True
  | x :: xs, s :: ss => x.render = s.toUTF8 ∧ RendersAs xs ss
  | _, _ => False

theorem RendersAs.append : ∀ {a b : List Obj} {s t : List String}, RendersAs a s → RendersAs b t →
    RendersAs (a ++ b) (s ++ t)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨hx, ha⟩, h => ⟨hx, RendersAs.append ha h⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem renderList_intercalate (acc : ByteArray) :
    ∀ (xs : List Obj) (ss : List String), RendersAs xs ss →
      Obj.renderList acc xs = acc ++ (" ".intercalate ss).toUTF8
  | [], [], _ => by simp [Obj.renderList]
  | [x], [s], ⟨hx, _⟩ => by
    simp only [Obj.renderList, String.intercalate_singleton, ← hx]
    exact PdfRead.Obj.renderInto_exact acc x
  | x :: y :: rest, s :: t :: ss, ⟨hx, hr⟩ => by
    rw [show Obj.renderList acc (x :: y :: rest) = Obj.renderList ((Obj.renderInto acc x).push 32) (y :: rest)
      from rfl, renderList_intercalate _ (y :: rest) (t :: ss) hr,
      PdfRead.Obj.renderInto_exact, push_space, String.intercalate_cons_cons, PdfRead.utf8_append,
      PdfRead.utf8_append, hx]
    simp only [ByteArray.append_assoc]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | [_], _ :: _ :: _, ⟨_, h⟩ => h.elim
  | _ :: _ :: _, [_], ⟨_, h⟩ => h.elim

theorem arr_render (xs : List Obj) (ss : List String) (h : RendersAs xs ss) :
    (Obj.arr xs.toArray).render = ("[" ++ " ".intercalate ss ++ "]").toUTF8 := by
  change (Obj.renderList (ByteArray.empty.push 91) xs.toArray.toList).push 93 = _
  rw [List.toList_toArray, renderList_intercalate _ xs ss h, PdfRead.utf8_append, PdfRead.utf8_append]
  have h1 : "[".toUTF8 = ByteArray.empty.push 91 := by rw [String.toUTF8_eq_toByteArray]; rfl
  have h2 : "]".toUTF8 = ByteArray.empty.push 93 := by rw [String.toUTF8_eq_toByteArray]; rfl
  rw [h1, h2]
  apply ByteArray.ext
  simp only [ByteArray.data_push, ByteArray.data_append]
  simp

theorem toUInt8_toNat (c : Char) : Nat.toUInt8 c.toNat = c.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  exact UInt8.toNat_ofNat.symm

theorem strChars_render (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) :
    (PdfRead.strOf (cs.map Char.toNat)).render = (String.ofList cs).toUTF8 := by
  rw [PdfLex.ascii_utf8 _ h]
  simp only [PdfRead.strOf, Obj.render, Obj.renderInto, ByteArray.empty_append, List.map_map]
  apply ByteArray.ext
  simp only [List.data_toByteArray]
  simp [Function.comp_def, toUInt8_toNat]

/-! ### A `TJ` array's elements -/

/-- The hex string a glyph run spells. -/
def gidS (gs : List Nat) : String :=
  String.singleton '<' ++ String.join (gs.map gidHex) ++ String.singleton '>'

/-- `kernedObjs`'s elements as the writer spells them. -/
def kernedStrs : List (Nat × Int) → List Nat → List String
  | [], cur => [gidS cur]
  | (g, n) :: rest, cur =>
    if n != 0 then gidS cur :: toString n :: kernedStrs rest [g] else kernedStrs rest (cur ++ [g])

theorem gidHex_hex (g : Nat) : ∀ c ∈ (gidHex g).toList, ∃ k, c = Hex.spell true k := by
  intro c hc
  rw [gidHex_toList] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem join_hex (gs : List Nat) : ∀ c ∈ (String.join (gs.map gidHex)).toList, ∃ k, c = Hex.spell true k := by
  intro c hc
  rw [String.toList_join] at hc
  obtain ⟨l, hl, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp ht
  exact gidHex_hex g c hc

theorem gidS_chars (gs : List Nat) :
    (gidS gs).toList = '<' :: (String.join (gs.map gidHex)).toList ++ ['>'] := by
  simp [gidS, String.toList_append]

theorem gidS_ascii (gs : List Nat) : ∀ c ∈ (gidS gs).toList, c.toNat < 128 := by
  intro c hc
  rw [gidS_chars] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨k, rfl⟩ := join_hex gs c hc
    exact Hex.spell_ascii true k
  · rw [List.mem_singleton.mp hc]; decide

theorem gidStr_eq (gs : List Nat) : gidStr gs = PdfRead.strOf ((gidS gs).toList.map Char.toNat) := by
  rw [gidS_chars]
  simp [gidStr, hexObj]

theorem gidStr_render (gs : List Nat) : (gidStr gs).render = (gidS gs).toUTF8 := by
  rw [gidStr_eq, strChars_render _ (gidS_ascii gs), String.ofList_toList]

theorem gidStr_spelled (gs : List Nat) : PdfContentLex.ValSpelled (gidStr gs) := by
  refine ⟨?_, fun n g h => by simp [gidStr, hexObj, PdfRead.strOf] at h⟩
  have hd : ∀ c ∈ (String.join (gs.map gidHex)).toList, c.toNat < 256 ∧ Hex.val? c.toNat ≠ none :=
    fun c hc => PdfRead.hexDigit_spelled c (join_hex gs c hc)
  apply PdfRead.strOf_representable
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · decide
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact (hd c hc).1
    · rw [List.mem_singleton.mp hb]; decide
  · refine .hex fun b hb => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact Or.inl (hd c hc).2

theorem kerned_rel : ∀ (l : List (Nat × Int)) (cur : List Nat),
    RendersAs (kernedObjs l cur) (kernedStrs l cur)
  | [], cur => ⟨gidStr_render cur, trivial⟩
  | (g, n) :: rest, cur => by
    simp only [kernedObjs, kernedStrs]
    split
    · exact ⟨gidStr_render cur, rfl, kerned_rel rest [g]⟩
    · exact kerned_rel rest (cur ++ [g])

theorem kern_fold : ∀ (l : List (Nat × Int)) (A : Array String) (cur : List Nat),
    (let r := l.foldl kernStep (A, String.singleton '<' ++ String.join (cur.map gidHex))
     (r.1.push (r.2 ++ String.singleton '>')).toList) = A.toList ++ (kernedStrs l cur)
  | [], A, cur => by simp [kernedStrs, gidS]
  | (g, n) :: rest, A, cur => by
    simp only [List.foldl_cons, kernStep_eq, kernedStrs]
    split
    · have h := kern_fold rest ((A.push (String.singleton '<' ++ String.join (cur.map gidHex) ++
        String.singleton '>')).push (toString n)) [g]
      simp only [List.map_cons, List.map_nil, String.join_cons, String.join_nil, String.append_empty] at h
      simp only [h, Array.toList_push, gidS, List.append_assoc, List.cons_append, List.nil_append]
    · have h := kern_fold rest A (cur ++ [g])
      simp only [List.map_append, List.map_cons, List.map_nil, String.join_append, String.join_cons,
        String.join_nil, String.append_empty] at h
      simpa only [String.append_assoc] using h

theorem item_rel (it : TextItem) : RendersAs (TextItem.objs it) it.parts.toList := by
  rw [TextItem.parts_eq]
  cases it with
  | glyphs gids => exact ⟨gidStr_render gids.toList, trivial⟩
  | adjust d => exact ⟨rfl, trivial⟩
  | kerned gids nums =>
    simp only [TextItem.objs]
    rw [← Array.foldl_toList, Array.toList_zipIdx]
    have h := kern_fold (gids.toList.zipIdx.map fun (g, i) => (g, nums.getD i 0)) #[] []
    simp only [List.map_nil, String.join_nil, String.append_empty, List.foldl_map, List.nil_append] at h
    rw [show String.singleton '<' = "<" by decide] at h
    rw [h]
    exact kerned_rel _ []

theorem items_rel : ∀ (l : List TextItem),
    RendersAs (l.flatMap TextItem.objs) (l.flatMap fun it => it.parts.toList)
  | [] => trivial
  | it :: rest => by
    simp only [List.flatMap_cons]
    exact (item_rel it).append (items_rel rest)

theorem kerned_spelled : ∀ (l : List (Nat × Int)) (cur : List Nat),
    ∀ x ∈ kernedObjs l cur, PdfContentLex.ValSpelled x
  | [], cur => by simp only [kernedObjs, List.mem_singleton]; rintro x rfl; exact gidStr_spelled cur
  | (g, n) :: rest, cur => by
    simp only [kernedObjs]
    split
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact gidStr_spelled cur
      · exact ⟨.int _, fun _ _ h => by cases h⟩
      · exact kerned_spelled rest [g] x hx
    · exact kerned_spelled rest (cur ++ [g])

theorem item_spelled (it : TextItem) : ∀ x ∈ TextItem.objs it, PdfContentLex.ValSpelled x := by
  cases it with
  | glyphs gids => simp only [TextItem.objs, List.mem_singleton]; rintro x rfl; exact gidStr_spelled _
  | adjust d => simp only [TextItem.objs, List.mem_singleton]; rintro x rfl; exact ⟨.int _, fun _ _ h => by cases h⟩
  | kerned gids nums => exact kerned_spelled _ []

/-! ### The writer's text operators as words -/

/-- An operand word. -/
def valW (o : Obj) (str : String) : Word := ⟨.val o, str, 32⟩

/-- A name operand's word. -/
def nameW (n : String) : Word := valW (.name n) ("/" ++ PdfLex.escapeName n)

/-- A number string's word. -/
def numW (s : String) : Word := valW (numObj s) s

/-- A colour's fill operators' words. -/
def colorWordsT (c : Ir.Color) : List Word :=
  match c.pdfModel with
  | some (.rgb r g b) => [numW r, numW g, numW b, opW "rg"]
  | some (.gray v) => [numW v, opW "g"]
  | some (.cmyk cy m y k) => [numW cy, numW m, numW y, numW k, opW "k"]
  | some (.separation i t) => [nameW i.resKey, opW "cs", ratW t.num t.den, opW "scn"]
  | none =>
    match c.cmyk with
    | some (cy, m, y, k) => [milliW cy, milliW m, milliW y, milliW k, opW "k"]
    | none => colorWords c ++ [opW "rg"]

/-- A one-entry dictionary's spelling around its value's. -/
def dict1S (k v : String) : String := "<< /" ++ PdfLex.escapeName k ++ " " ++ v ++ " >>"

/-- A text string's characters, each one byte (`PdfRead.textStringBytes`). -/
def litChar (c : Char) : List Char :=
  if c = '(' ∨ c = ')' ∨ c = '\\' then ['\\', c] else if c = '\r' then ['\\', 'r'] else [c]

def tsChars (a : String) : List Char :=
  if a.toList.all PdfRead.docEncodingSelf then '(' :: a.toList.flatMap litChar ++ [')']
  else '<' :: ("FEFF" ++ String.join (a.toList.map PdfRead.utf16Hex)).toList ++ ['>']

/-- A marked sequence's opening words. -/
def tagWords : MarkTag → List Word
  | .artifact none => [nameW "Artifact", opW "BMC"]
  | .artifact (some k) =>
    [nameW "Artifact", valW (.dict #[("Type", .name (kindName k))]) (dict1S "Type" ("/" ++ kindName k)),
     opW "BDC"]
  | .content s mcid _ =>
    [nameW s, valW (.dict #[("MCID", .int mcid)]) (dict1S "MCID" (toString mcid)), opW "BDC"]
  | .span a =>
    [nameW "Span", valW (.dict #[("ActualText", PdfRead.textString a)])
      (dict1S "ActualText" (String.ofList (tsChars a))), opW "BDC"]

/-- A `TJ` array's word. -/
def tjW (items : Array TextItem) : Word :=
  valW (.arr (items.toList.flatMap TextItem.objs).toArray)
    ("[" ++ " ".intercalate (items.toList.flatMap fun it => it.parts.toList) ++ "]")

mutual

/-- A text operator's words, each operator ending its line. -/
def textWords : TextOp → List Word
  | .scale p => endLine [valW (scaleObj p) s!"{p / 10}.{p % 10}", opW "Tz"]
  | .move x y => endLine [natW 1, natW 0, natW 0, natW 1, lenW x, lenW y, opW "Tm"]
  | .font r size => endLine [nameW s!"F{r + 1}", lenW size, opW "Tf"]
  | .color c => endLine (colorWordsT c)
  | .show items => endLine [tjW items, opW "TJ"]
  | .marked t body => endLine (tagWords t) ++ textWordsList body.toList ++ [(opW "EMC").nl]

def textWordsList : List TextOp → List Word
  | [] => []
  | o :: rest =>
    let tail := textWordsList rest
    textWords o ++ tail

end

theorem colorWordsT_tok (c : Ir.Color) :
    (colorWordsT c).map (·.tok) = (colorToks c).flatMap fun (vs, n) => vs.map .val ++ [.op n] := by
  unfold colorWordsT colorToks
  split
  · rfl
  · rfl
  · rfl
  · simp [nameW, valW, opW, ratW_tok]
  · split <;> rfl

theorem tagWords_tok (t : MarkTag) : (tagWords t).map (·.tok) = tagToks t := by
  cases t with
  | artifact k => cases k <;> rfl
  | content s mcid leaf => rfl
  | span a => rfl

mutual

theorem textWords_tok : ∀ o : TextOp, (textWords o).map (·.tok) = TextOp.toks writerSpell o
  | .scale p => by simp [textWords, endLine_tok]; rfl
  | .move x y => by simp [textWords, endLine_tok]; rfl
  | .font r size => by simp [textWords, endLine_tok]; rfl
  | .color c => by
    rw [textWords, endLine_tok, colorWordsT_tok, TextOp.toks]
    rfl
  | .show items => by simp [textWords, endLine_tok]; rfl
  | .marked t body => by
    rw [textWords, TextOp.toks, List.map_append, List.map_append, endLine_tok, tagWords_tok,
      textWordsList_tok body.toList]
    rfl

theorem textWordsList_tok : ∀ l : List TextOp,
    (textWordsList l).map (·.tok) = TextOp.toksList writerSpell l
  | [] => rfl
  | o :: rest => by
    rw [textWordsList, TextOp.toksList, List.map_append, textWords_tok o, textWordsList_tok rest]

end

/-! ### The words spell the writer's characters -/

@[simp] theorem esc_artifact : PdfLex.escapeName "Artifact" = "Artifact" :=
  escapeName_plain _ (by decide) (by decide)
@[simp] theorem esc_span : PdfLex.escapeName "Span" = "Span" := escapeName_plain _ (by decide) (by decide)
@[simp] theorem esc_type : PdfLex.escapeName "Type" = "Type" := escapeName_plain _ (by decide) (by decide)
@[simp] theorem esc_mcid : PdfLex.escapeName "MCID" = "MCID" := escapeName_plain _ (by decide) (by decide)
@[simp] theorem esc_actual : PdfLex.escapeName "ActualText" = "ActualText" :=
  escapeName_plain _ (by decide) (by decide)

theorem esc_kind (k : ArtifactKind) : PdfLex.escapeName (kindName k) = kindName k := by
  cases k <;> exact escapeName_plain _ (by decide) (by decide)

theorem digit_keeps (c : Char) (h : c.isDigit = true) : PdfLex.nameKeeps c = true := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : 48 ≤ c.toNat := by have := h.1; simp [UInt32.le_iff_toNat_le] at this; exact this
  have h2 : c.toNat ≤ 57 := by have := h.2; simp [UInt32.le_iff_toNat_le] at this; exact this
  simp only [PdfLex.nameKeeps, PdfLex.isDelim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
  generalize c.toNat = n at h1 h2
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

@[simp] theorem ofNat_space : Char.ofNat 32 = ' ' := rfl
@[simp] theorem ofNat_nl : Char.ofNat 10 = '\n' := rfl

theorem esc_font (r : Nat) : PdfLex.escapeName s!"F{r}" = s!"F{r}" := by
  apply escapeName_plain _ (fun h => by
    have := congrArg String.toList h
    simp [String.toList_append, ts] at this)
  intro c hc
  simp only [String.toList_append, List.mem_append, ts] at hc
  rcases hc with hc | hc
  · have : c = 'F' := by simpa using hc
    subst this; decide
  · exact digit_keeps c (toDigits_digits r c (by simpa [Nat.toString_eq_repr, Nat.toList_repr] using hc))

theorem litChar_bytes (c : Char) : PdfRead.literalByte c.toNat = (litChar c).map Char.toNat := by
  have hc : ∀ n : Nat, c.toNat = n → c = Char.ofNat n := fun n h => by rw [← h, Char.ofNat_toNat]
  unfold PdfRead.literalByte litChar
  by_cases h1 : c = '(' ∨ c = ')' ∨ c = '\\'
  · rw [ite_eq_left h1]
    have : (c.toNat == 40 || c.toNat == 41 || c.toNat == 92) = true := by
      rcases h1 with rfl | rfl | rfl <;> decide
    rw [ite_eq_left this]
    rfl
  · rw [ite_eq_right h1]
    have : ¬ (c.toNat == 40 || c.toNat == 41 || c.toNat == 92) = true := by
      intro h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (h | h) | h
      · exact h1 (Or.inl (hc 40 h))
      · exact h1 (Or.inr (Or.inl (hc 41 h)))
      · exact h1 (Or.inr (Or.inr (hc 92 h)))
    rw [ite_eq_right this]
    by_cases h2 : c = '\r'
    · subst h2; rfl
    · rw [ite_eq_right h2]
      have : ¬ (c.toNat == 13) = true := by
        intro h; exact h2 (hc 13 (by simpa using h))
      rw [ite_eq_right this]
      rfl

theorem textStringBytes_chars (a : String) : PdfRead.textStringBytes a = (tsChars a).map Char.toNat := by
  unfold PdfRead.textStringBytes tsChars
  split
  · simp only [PdfRead.literalBytes, List.map_cons, List.map_append, List.map_flatMap, List.flatMap_map,
      litChar_bytes]
    rfl
  · simp

theorem tsChars_ascii (a : String) : ∀ c ∈ tsChars a, c.toNat < 128 := by
  unfold tsChars
  split
  · next hall =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
      have hs := List.all_eq_true.mp hall d hd
      have hd' : d.toNat < 128 := by
        simp only [PdfRead.docEncodingSelf, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hs
        rcases hs with ((h | rfl) | rfl) | rfl
        · omega
        all_goals decide
      unfold litChar at hc
      split at hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · decide
        · rw [List.mem_singleton.mp hc]; exact hd'
      · split at hc
        · rcases List.mem_cons.mp hc with rfl | hc
          · decide
          · rw [List.mem_singleton.mp hc]; decide
        · rw [List.mem_singleton.mp hc]; exact hd'
    · rw [List.mem_singleton.mp hc]; decide
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    rcases List.mem_append.mp hc with hc | hc
    · simp only [String.toList_append, List.mem_append] at hc
      rcases hc with hc | hc
      · have : c ∈ ['F', 'E', 'F', 'F'] := by simpa using hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl | rfl <;> decide
      · rw [String.toList_join] at hc
        obtain ⟨l, hl, hc⟩ := List.mem_flatten.mp hc
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
        obtain ⟨k, rfl⟩ := PdfRead.utf16Hex_spelled d c hc
        exact Hex.spell_ascii true k
    · rw [List.mem_singleton.mp hc]; decide

theorem textString_render (a : String) :
    (PdfRead.textString a).render = (String.ofList (tsChars a)).toUTF8 := by
  rw [PdfRead.textString, textStringBytes_chars]
  exact strChars_render _ (tsChars_ascii a)

theorem opener_span (a : String) :
    String.ofList ((PdfRead.textStringBytes a).map Char.ofNat) = String.ofList (tsChars a) := by
  rw [textStringBytes_chars, List.map_map]
  congr 1
  conv => rhs; rw [← List.map_id (tsChars a)]
  apply List.map_congr_left
  intro c _
  exact Char.ofNat_toNat c

theorem dict1_render (k : String) (v : Obj) (vs : String) (hv : v.render = vs.toUTF8) :
    (Obj.dict #[(k, v)]).render = (dict1S k vs).toUTF8 := by
  change Obj.renderEntries (ByteArray.empty ++ "<< ".toUTF8) [(k, v)] ++ ">>".toUTF8 = _
  simp only [Obj.renderEntries, PdfRead.Obj.renderInto_exact, push_space, hv, ← PdfRead.utf8_append,
    ByteArray.empty_append]
  congr 1
  simp only [dict1S, String.append_assoc]
  apply String.ext
  simp [String.toList_append]

theorem colorWordsT_chars (c : Ir.Color) :
    (c.pdfFill ++ "\n").toList = wordsChars (endLine (colorWordsT c)) := by
  rw [Ir.Color.pdfFill_eq]
  unfold colorWordsT
  cases h : c.pdfModel with
  | none =>
    cases h' : c.cmyk with
    | none =>
      simp only [colorWords, milliW, opW, endLine, Word.nl, wordsChars_cons, wordsChars_nil, sep_space,
        sep_nl, String.toList_append, components_chars, List.append_assoc, List.cons_append,
        List.nil_append]
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.r) = x
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.g) = y
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.b) = z
      simp
    | some q =>
      obtain ⟨cy, m, y, k⟩ := q
      simp [milliW, opW, endLine, Word.nl, String.toList_append]
  | some p =>
    cases p with
    | rgb r g b => simp [numW, valW, opW, endLine, Word.nl, String.toList_append]
    | gray v => simp [numW, valW, opW, endLine, Word.nl, String.toList_append]
    | cmyk a b d e => simp [numW, valW, opW, endLine, Word.nl, String.toList_append]
    | separation i t =>
      simp only [nameW, valW, ratW, opW, endLine, Word.nl, wordsChars_cons, wordsChars_nil, sep_space,
        sep_nl, String.toList_append, List.append_assoc]
      generalize PdfLex.escapeName i.resKey = e
      generalize Dim.ratString t.num t.den = q
      simp

theorem tagWords_chars (t : MarkTag) :
    (t.opener ++ "\n").toList = wordsChars (endLine (tagWords t)) := by
  cases t with
  | artifact k =>
    cases k with
    | none => simp [MarkTag.opener, tagWords, nameW, valW, opW, endLine, Word.nl]
    | some k =>
      cases k <;> simp [MarkTag.opener, tagWords, nameW, valW, opW, endLine, Word.nl, dict1S, kindName]
  | content s mcid leaf =>
    simp [MarkTag.opener, tagWords, nameW, valW, opW, endLine, Word.nl, dict1S, ts]
  | span a =>
    simp only [MarkTag.opener, opener_span]
    simp [tagWords, nameW, valW, opW, endLine, Word.nl, dict1S, String.toList_append]

theorem renderLines_join (acc : String) (l : List TextOp) :
    TextOp.renderLines acc l = acc ++ String.join (l.map fun o => o.render ++ "\n") := by
  induction l generalizing acc with
  | nil => simp [TextOp.renderLines, String.join_nil]
  | cons o rest ih =>
    rw [TextOp.renderLines, ih, List.map_cons, String.join_cons]
    simp [String.append_assoc]

mutual

theorem textWords_chars : ∀ o : TextOp, (o.render ++ "\n").toList = wordsChars (textWords o)
  | .scale p => by
    simp only [TextOp.render, textWords, valW, opW, endLine, Word.nl, wordsChars_cons, wordsChars_nil,
      sep_space, sep_nl, String.toList_append]
    generalize toString (p / 10) = a
    generalize toString (p % 10) = b
    simp [ts]
  | .move x y => by
    simp only [TextOp.render, textWords, natW, lenW, opW, endLine, Word.nl, wordsChars_cons,
      wordsChars_nil, sep_space, sep_nl, String.toList_append]
    generalize x.toBpString = a
    generalize y.toBpString = b
    simp [ts, show Nat.toDigits 10 1 = ['1'] by decide]
  | .font r size => by
    simp only [TextOp.render, textWords, nameW, valW, lenW, opW, endLine, Word.nl, wordsChars_cons,
      wordsChars_nil, sep_space, sep_nl, String.toList_append, esc_font]
    generalize size.toBpString = a
    simp [ts]
  | .color c => by
    rw [TextOp.render, textWords]
    exact colorWordsT_chars c
  | .show items => by
    simp only [TextOp.render, textWords, tjW, valW, opW, endLine, Word.nl, wordsChars_cons,
      wordsChars_nil, sep_space, sep_nl, String.toList_append]
    generalize " ".intercalate (items.toList.flatMap fun it => it.parts.toList) = a
    simp
  | .marked t body => by
    rw [TextOp.render, renderLines_join, textWords]
    simp only [String.toList_append, wordsChars_append, ← tagWords_chars, ← textWordsList_chars body.toList]
    simp [opW, Word.nl, List.append_assoc]

theorem textWordsList_chars : ∀ l : List TextOp,
    (String.join (l.map fun o => o.render ++ "\n")).toList = wordsChars (textWordsList l)
  | [] => by simp [String.join_nil, textWordsList]
  | o :: rest => by
    rw [List.map_cons, String.join_cons, String.toList_append, textWords_chars o,
      textWordsList_chars rest, textWordsList, wordsChars_append]

end

/-! ### Each word reads back -/

theorem ofNat_lt (n : Nat) (h : n < 256) : (Char.ofNat n).toNat < 256 := by
  unfold Char.ofNat
  split
  · simp [Char.ofNatAux, Char.toNat]; exact h
  · decide

theorem resKey_spelled (i : Ir.Ink) : Obj.NameSpelling i.resKey := by
  refine ⟨fun h => by
    have := congrArg String.toList h
    simp [Ir.Ink.resKey, String.toList_append] at this, ?_⟩
  intro c hc
  simp only [Ir.Ink.resKey, Ir.Ink.pdfName, String.toList_append, String.toList_ofList,
    List.mem_append, List.mem_map] at hc
  rcases hc with hc | ⟨b, _, rfl⟩
  · have : c ∈ ['I', 'n', 'k', '.'] := by simpa using hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · exact ofNat_lt _ b.toNat_lt

theorem valW_real (s : String) (hs : Obj.RealSpelling s) : WordOk (valW (.real s) s) :=
  ⟨by simp [valW, PdfContentLex.spell, Obj.render, Obj.renderInto], ⟨.real hs, fun _ _ h => by cases h⟩,
    Or.inl rfl⟩

theorem scale_spelled (p : Int) : Obj.RealSpelling s!"{p / 10}.{p % 10}" := by
  refine ⟨by simp [String.toList_append, ts], ?_⟩
  intro c hc
  simp only [String.toList_append, ts, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact PdfRead.int_numeric _ c hc
  · have : c = '.' := by simpa using hc
    subst this; decide
  · exact PdfRead.int_numeric _ c hc

theorem nameW_ok (n : String) (h : Obj.NameSpelling n) : WordOk (nameW n) :=
  ⟨by simp [nameW, valW, PdfContentLex.spell, Obj.render, Obj.renderInto], ⟨.name h, fun _ _ h => by cases h⟩,
    Or.inl rfl⟩

theorem dictW_ok (k : String) (v : Obj) (vs : String) (hk : Obj.NameSpelling k) (hv : v.render = vs.toUTF8)
    (hr : v.Representable) : WordOk (valW (.dict #[(k, v)]) (dict1S k vs)) := by
  refine ⟨dict1_render k v vs hv, ⟨.dict ?_ ?_, fun _ _ h => by cases h⟩, Or.inl rfl⟩
  · intro e he
    have he : e = (k, v) := by simpa using he
    subst he
    exact hk
  · intro e he
    have he : e = (k, v) := by simpa using he
    subst he
    exact hr

theorem tjW_ok (items : Array TextItem) : WordOk (tjW items) := by
  refine ⟨arr_render _ _ (items_rel items.toList), ⟨.arr fun x hx => ?_, fun _ _ h => by cases h⟩, Or.inl rfl⟩
  have hx : x ∈ items.toList.flatMap TextItem.objs := by simpa using hx
  obtain ⟨it, _, hx⟩ := List.mem_flatMap.mp hx
  exact (item_spelled it x hx).1

theorem tagWords_ok (t : MarkTag) (h : ∀ s m l, t = .content s m l → Obj.NameSpelling s) :
    ∀ w ∈ tagWords t, WordOk w := by
  cases t with
  | artifact k =>
    cases k with
    | none =>
      intro w hw
      simp only [tagWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact nameW_ok _ ⟨by decide, by decide⟩
      · exact opW_ok _ (by opspelled)
    | some k =>
      intro w hw
      simp only [tagWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact nameW_ok _ ⟨by decide, by decide⟩
      · refine dictW_ok _ _ _ ⟨by decide, by decide⟩ ?_ ?_
        · simp [Obj.render, Obj.renderInto, esc_kind]
        · exact .name (by cases k <;> exact ⟨by decide, by decide⟩)
      · exact opW_ok _ (by opspelled)
  | content s mcid leaf =>
    intro w hw
    simp only [tagWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact nameW_ok _ (h s mcid leaf rfl)
    · exact dictW_ok _ _ _ ⟨by decide, by decide⟩ (intRender mcid) (.int _)
    · exact opW_ok _ (by opspelled)
  | span a =>
    intro w hw
    simp only [tagWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact nameW_ok _ ⟨by decide, by decide⟩
    · exact dictW_ok _ _ _ ⟨by decide, by decide⟩ (textString_render a) (PdfRead.textString_representable a)
    · exact opW_ok _ (by opspelled)

theorem numW_ok (s : String) (h : NumSpelled s) : WordOk (numW s) := ⟨h.1, h.2, Or.inl rfl⟩

theorem colorWordsT_ok (c : Ir.Color) (h : ColorSpelled c) : ∀ w ∈ colorWordsT c, WordOk w := by
  unfold ColorSpelled at h
  unfold colorWordsT
  intro w hw
  split at h
  all_goals rename_i hm
  all_goals simp only [hm, List.mem_cons, List.not_mem_nil, or_false] at hw
  · obtain ⟨h1, h2, h3⟩ := h
    rcases hw with rfl | rfl | rfl | rfl
    · exact numW_ok _ h1
    · exact numW_ok _ h2
    · exact numW_ok _ h3
    · exact opW_ok _ (by opspelled)
  · rcases hw with rfl | rfl
    · exact numW_ok _ h
    · exact opW_ok _ (by opspelled)
  · obtain ⟨h1, h2, h3, h4⟩ := h
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact numW_ok _ h1
    · exact numW_ok _ h2
    · exact numW_ok _ h3
    · exact numW_ok _ h4
    · exact opW_ok _ (by opspelled)
  · rcases hw with rfl | rfl | rfl | rfl
    · exact nameW_ok _ (resKey_spelled _)
    · exact opW_ok _ (by opspelled)
    · exact ratW_ok _ _
    · exact opW_ok _ (by opspelled)
  · split at h
    all_goals rename_i hc
    all_goals simp only [hc, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hw
    · obtain ⟨h1, h2, h3, h4⟩ := h
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact milliW_ok _ h1
      · exact milliW_ok _ h2
      · exact milliW_ok _ h3
      · exact milliW_ok _ h4
      · exact opW_ok _ (by opspelled)
    · rcases hw with hw | rfl
      · exact colorWords_ok c w hw
      · exact opW_ok _ (by opspelled)

mutual

theorem textWords_ok : ∀ o : TextOp, TextOp.Spelled o → ∀ w ∈ textWords o, WordOk w
  | .scale p, _ => by
    refine endLine_ok _ ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact valW_real _ (scale_spelled p)
    · exact opW_ok _ (by opspelled)
  | .move x y, _ => by
    refine endLine_ok _ ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact natW_ok _
    · exact natW_ok _
    · exact natW_ok _
    · exact natW_ok _
    · exact lenW_ok _
    · exact lenW_ok _
    · exact opW_ok _ (by opspelled)
  | .font r size, _ => by
    refine endLine_ok _ ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · refine nameW_ok _ ⟨fun h => ?_, fun c hc => ?_⟩
      · have := congrArg String.toList h
        simp [String.toList_append, ts] at this
      · simp only [String.toList_append, ts, List.mem_append] at hc
        rcases hc with hc | hc
        · have : c = 'F' := by simpa using hc
          subst this; decide
        · have := toDigits_digits (r + 1) c (by simpa [Nat.toString_eq_repr, Nat.toList_repr] using hc)
          simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
          have := this.2
          simp [UInt32.le_iff_toNat_le] at this
          change c.toNat ≤ 57 at this
          omega
    · exact lenW_ok _
    · exact opW_ok _ (by opspelled)
  | .color c, h => endLine_ok _ (colorWordsT_ok c h)
  | .show items, _ => by
    refine endLine_ok _ ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact tjW_ok items
    · exact opW_ok _ (by opspelled)
  | .marked t body, h => by
    have hb : TextOp.SpelledList body.toList := by
      cases t <;> simp only [TextOp.Spelled] at h <;> first | exact h | exact h.2
    have ht : ∀ s m l, t = .content s m l → Obj.NameSpelling s := by
      intro s m l he
      subst he
      exact h.1
    intro w hw
    simp only [textWords, List.mem_append, List.mem_singleton] at hw
    rcases hw with (hw | hw) | rfl
    · exact endLine_ok _ (tagWords_ok t ht) w hw
    · exact textWordsList_ok body.toList hb w hw
    · exact nl_ok (opW_ok _ (by opspelled))

theorem textWordsList_ok : ∀ l : List TextOp, TextOp.SpelledList l → ∀ w ∈ textWordsList l, WordOk w
  | [], _ => by simp [textWordsList]
  | o :: rest, h => by
    intro w hw
    simp only [textWordsList, List.mem_append] at hw
    rcases hw with hw | hw
    · exact textWords_ok o h.1 w hw
    · exact textWordsList_ok rest h.2 w hw

end

/-! ### No operator the writer spells starts with `R` -/

theorem colorToks_ops (c : Ir.Color) :
    ∀ o ∈ colorToks c, o.2 = "rg" ∨ o.2 = "g" ∨ o.2 = "k" ∨ o.2 = "cs" ∨ o.2 = "scn" := by
  unfold colorToks
  split
  all_goals try split
  all_goals simp

theorem colorToks_noR (c : Ir.Color) :
    ∀ t ∈ (colorToks c).flatMap (fun (vs, n) => vs.map Tok.val ++ [Tok.op n]),
      PdfContentLex.leadR t = false := by
  intro t ht
  obtain ⟨o, ho, ht⟩ := List.mem_flatMap.mp ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    rfl
  · rw [List.mem_singleton.mp ht]
    rcases colorToks_ops c o ho with h | h | h | h | h <;> rw [h] <;> decide

theorem tagToks_noR (t : MarkTag) : ∀ u ∈ tagToks t, PdfContentLex.leadR u = false := by
  cases t with
  | artifact k => cases k <;> simp [tagToks, tagProps, PdfContentLex.leadR]
  | content s m l => simp [tagToks, tagProps, PdfContentLex.leadR]
  | span a => simp [tagToks, tagProps, PdfContentLex.leadR]

mutual

theorem toks_noR : ∀ o : TextOp, ∀ t ∈ TextOp.toks writerSpell o, PdfContentLex.leadR t = false
  | .scale _ => by simp [TextOp.toks, PdfContentLex.leadR]
  | .move _ _ => by simp [TextOp.toks, PdfContentLex.leadR]
  | .font _ _ => by simp [TextOp.toks, PdfContentLex.leadR]
  | .color c => by rw [TextOp.toks]; exact colorToks_noR c
  | .show _ => by simp [TextOp.toks, PdfContentLex.leadR]
  | .marked tg body => by
    intro t ht
    rw [TextOp.toks] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact tagToks_noR tg t ht
    · exact toksList_noR body.toList t ht
    · decide

theorem toksList_noR : ∀ l : List TextOp, ∀ t ∈ TextOp.toksList writerSpell l,
    PdfContentLex.leadR t = false
  | [] => by simp [TextOp.toksList]
  | o :: rest => by
    intro t ht
    rw [TextOp.toksList] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact toks_noR o t ht
    · exact toksList_noR rest t ht

end

theorem spelled_of : ∀ (l : List Tok), (∀ t ∈ l, PdfContentLex.TokSpelled t) →
    (∀ t ∈ l, PdfContentLex.leadR t = false) → PdfContentLex.Spelled l
  | [], _, _ => trivial
  | t :: rest, ht, hr =>
    ⟨ht t (by simp), fun _ _ _ u hu => hr u (by
      cases rest with
      | nil => simp at hu
      | cons v vs => simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hu; subst hu; simp),
     spelled_of rest (fun u hu => ht u (by simp [hu])) (fun u hu => hr u (by simp [hu]))⟩

/-! ### The text object -/

/-- A text object's words: `BT`, its operators', `ET`. -/
def objWords (ops : Array TextOp) : List Word :=
  ((opW "BT").nl :: textWordsList ops.toList) ++ [(opW "ET").nl]

theorem objWords_tok (ops : Array TextOp) :
    (objWords ops).map (·.tok) = [Tok.op "BT"] ++ TextOp.toksList writerSpell ops.toList ++ [Tok.op "ET"] := by
  simp [objWords, textWordsList_tok, opW, Word.nl]

theorem objWords_ok (ops : Array TextOp) (h : TextOp.SpelledList ops.toList) :
    ∀ w ∈ objWords ops, WordOk w := by
  intro w hw
  simp only [objWords, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hw
  rcases hw with (rfl | hw) | rfl
  · exact nl_ok (opW_ok _ (by opspelled))
  · exact textWordsList_ok _ h w hw
  · exact nl_ok (opW_ok _ (by opspelled))

theorem objWords_chars (ops : Array TextOp) :
    ((ContentOp.text ops).render ++ "\n").toList = wordsChars (objWords ops) := by
  rw [text_render_exact]
  simp only [String.toList_append, objWords, wordsChars_cons, wordsChars_append, ← textWordsList_chars]
  simp [opW, Word.nl, List.append_assoc]

theorem text_bytes (ops : Array TextOp) (h : TextOp.SpelledList ops.toList) :
    (ContentOp.text ops).render.toUTF8 =
      PdfContentLex.renderSep false ((objWords ops).map fun w => (w.tok, w.sep)) := by
  have hne : (objWords ops).map (fun w => (w.tok, w.sep)) ≠ [] := by simp [objWords]
  have hlast : (((objWords ops).map fun w => (w.tok, w.sep)).getLast hne).2 = 10 := by
    simp only [objWords, List.map_append, List.map_cons, List.map_nil, List.getLast_concat]
    rfl
  have hb : ((ContentOp.text ops).render ++ "\n").toUTF8 = (wordsChars (objWords ops)).utf8Encode := by
    rw [toUTF8_chars, objWords_chars]
  rw [words_bytes _ (objWords_ok ops h), PdfContentLex.renderSep_true _ hne, hlast] at hb
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_append] at hb
  have hnl : "\n".toByteArray = ⟨#[10]⟩ := rfl
  rw [hnl, ← String.toUTF8_eq_toByteArray] at hb
  exact bytes_cancel _ _ _ hb

/-- The bytes the writer spells for a text object, whose colours and tags hold the writer's
spellings, scan back as `BT`, its operators' tokens in the writer's spelling, and `ET`. -/
public theorem scan_render_text (ops : Array TextOp) (h : TextOp.SpelledList ops.toList) :
    PdfContentLex.scan (ContentOp.render (.text ops)).toUTF8 =
      ([Tok.op "BT"] ++ TextOp.toksList writerSpell ops.toList ++ [Tok.op "ET"]).toArray := by
  rw [text_bytes ops h, PdfContentLex.scan_renderSep_exact]
  · simp only [List.map_map]
    rw [← objWords_tok]
    rfl
  · rw [List.map_map]
    show PdfContentLex.Spelled ((objWords ops).map (·.tok))
    exact spelled_of _
      (fun t ht => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht; exact (objWords_ok ops h w hw).tok)
      (fun t ht => by
        rw [objWords_tok] at ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with (rfl | ht) | rfl
        · decide
        · exact toksList_noR _ t ht
        · decide)
  · intro t ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    rcases (objWords_ok ops h w hw).sep with hs | hs <;> simp [hs] <;> decide

public theorem writerSpell_quiet : ∀ c, ∀ o ∈ writerSpell.color c, quietOp o.2 = true := by
  intro c o ho
  rcases colorToks_ops c o ho with h | h | h | h | h <;> rw [h] <;> decide

/-- The text a text object the writer spells reads as from its bytes, its colours and tags holding
the writer's spellings: each string's glyphs' text through `T` in the font the last `Tf` set, a
span's actual text for its glyphs, in operator order. -/
public theorem extract_text_bytes (res : Res) (T : Nat → Nat → String) (hT : FontReads res T)
    (ops : Array TextOp) (h : TextOp.SpelledList ops.toList) :
    itemsText (readToks res .unmarked (PdfContentLex.scan (ContentOp.render (.text ops)).toUTF8)).1 =
      (TextOp.shownList res T false none ops.toList).2 := by
  rw [scan_render_text ops h]
  exact extract_text res writerSpell T writerSpell_quiet hT ops

end LeanTex.Core.PdfContent
