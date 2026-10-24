module

public import LeanTex.Core.PdfContent
public import LeanTex.Core.PdfTextRead
public import LeanTex.Core.PdfText
public import LeanTex.Core.PdfToUnicode
import LeanTex.Core.PdfToUnicodeProof

/-! The text a viewer reads off the writer's text operators: the reader's interpretation of their
tokens shows each string's codes through the font the last `Tf` set, a span's actual text in place
of its glyphs, in operator order. -/

namespace LeanTex.Core.PdfContent

open LeanTex.Core LeanTex.Core.Pdf LeanTex.Core.Dim
open LeanTex.Core.PdfContentLex (Tok)
open LeanTex.Core.PdfRead (Obj)
open LeanTex.Core.PdfTextRead

/-! ### The writer's text operators as tokens -/

/-- How the writer spells the operands a text reading reads past: lengths, a scaling, and a
colour's operators, each with its operands. -/
public structure Spell where
  len : Length → Obj
  scale : Int → Obj
  color : Ir.Color → List (List Obj × String)

/-- Glyph ids as the hex string the writer spells. -/
@[expose] public def gidStr (gs : List Nat) : Obj := hexObj (String.join (gs.map gidHex))

/-- A kerned run's `TJ` elements: hex strings of its glyphs, a number before each glyph its kern
moves. -/
@[expose] public def kernedObjs : List (Nat × Int) → List Nat → List Obj
  | [], cur => [gidStr cur]
  | (g, n) :: rest, cur =>
    if n != 0 then gidStr cur :: .int n :: kernedObjs rest [g] else kernedObjs rest (cur ++ [g])

/-- A `TJ` element's spelling as objects. -/
@[expose] public def TextItem.objs : TextItem → List Obj
  | .glyphs gids => [gidStr gids.toList]
  | .kerned gids nums => kernedObjs (gids.toList.zipIdx.map fun (g, i) => (g, nums.getD i 0)) []
  | .adjust d => [.int d]

/-- A `TJ` element's glyph ids. -/
@[expose] public def TextItem.gids : TextItem → List Nat
  | .glyphs gids => gids.toList
  | .kerned gids _ => gids.toList
  | .adjust _ => []

/-- An artifact type's name. -/
@[expose] public def kindName : ArtifactKind → String
  | .pagination => "Pagination"
  | .layout => "Layout"
  | .page => "Page"

/-- The properties a marked sequence opens with. -/
@[expose] public def tagProps : MarkTag → Option Obj
  | .artifact none => none
  | .artifact (some k) => some (.dict #[("Type", .name (kindName k))])
  | .content _ mcid _ => some (.dict #[("MCID", .int mcid)])
  | .span a => some (.dict #[("ActualText", PdfRead.textString a)])

/-- The tag a marked sequence opens with. -/
@[expose] public def tagName : MarkTag → String
  | .artifact _ => "Artifact"
  | .content s _ _ => s
  | .span _ => "Span"

/-- A marked sequence's opening tokens. -/
@[expose] public def tagToks (t : MarkTag) : List Tok :=
  match tagProps t with
  | none => [.val (.name (tagName t)), .op "BMC"]
  | some p => [.val (.name (tagName t)), .val p, .op "BDC"]

mutual

/-- A text operator's tokens. -/
@[expose] public def TextOp.toks (sp : Spell) : TextOp → List Tok
  | .scale p => [.val (sp.scale p), .op "Tz"]
  | .move x y =>
    [.val (.int 1), .val (.int 0), .val (.int 0), .val (.int 1), .val (sp.len x), .val (sp.len y),
     .op "Tm"]
  | .font res size => [.val (.name s!"F{res + 1}"), .val (sp.len size), .op "Tf"]
  | .color c => (sp.color c).flatMap fun (vs, n) => vs.map .val ++ [.op n]
  | .show items => [.val (.arr (items.toList.flatMap TextItem.objs).toArray), .op "TJ"]
  | .marked t body => tagToks t ++ TextOp.toksList sp body.toList ++ [.op "EMC"]

@[expose] public def TextOp.toksList (sp : Spell) : List TextOp → List Tok
  | [] => []
  | o :: rest =>
    let tail := TextOp.toksList sp rest
    TextOp.toks sp o ++ tail

end

/-- The text a span's actual text reads as, where it reads. -/
@[expose] public def spanText? (a : String) : Option String :=
  actualOf (some (.dict #[("ActualText", PdfRead.textString a)]))

mutual

/-- What a text operator shows from the font resource a `Tf` last set: its glyphs' text through
`T`, none where a span already replaces the text, a span's actual text for its glyphs; with the
font resource in force after it. -/
@[expose] public def TextOp.shown (res : Res) (T : Nat → Nat → String) (inSpan : Bool)
    (k : Option Nat) : TextOp → Option Nat × String
  | .scale _ | .move _ _ | .color _ => (k, "")
  | .font r _ => ((res.fonts.get? s!"F{r + 1}").map fun _ => r, "")
  | .show items =>
    (k, if inSpan then "" else match k with
      | some r => String.join ((items.toList.flatMap TextItem.gids).map (T r))
      | none => "")
  | .marked (.span a) body =>
    match spanText? a with
    | some s => ((TextOp.shownList res T true k body.toList).1, if inSpan then "" else s)
    | none => TextOp.shownList res T inSpan k body.toList
  | .marked (.artifact _) body | .marked (.content _ _ _) body =>
    TextOp.shownList res T inSpan k body.toList

@[expose] public def TextOp.shownList (res : Res) (T : Nat → Nat → String) (inSpan : Bool)
    (k : Option Nat) : List TextOp → Option Nat × String
  | [] => (k, "")
  | o :: rest =>
    let r := TextOp.shown res T inSpan k o
    let r' := TextOp.shownList res T inSpan r.1 rest
    (r'.1, r.2 ++ r'.2)

end

/-- The text an item stands for, a form's none. -/
@[expose] public def Item.text? : Item → Option String
  | .text _ _ s => some s
  | .form .. => none

/-- The text a reading's items stand for, in order. -/
@[expose] public def itemsText (items : Array Item) : String :=
  String.join (items.toList.filterMap Item.text?)

theorem itemsText_push_text (items : Array Item) (m : Mark) (b : Brk) (s : String) :
    itemsText (items.push (.text m b s)) = itemsText items ++ s := by
  simp [itemsText, Item.text?, List.filterMap_append, String.join_append]

/-- What a step of the reader keeps: the open sequences, the font and the pending operands. -/
def Keeps (a b : St) : Prop :=
  b.opens = a.opens ∧ b.ts.font = a.ts.font ∧ b.args = a.args ∧ b.saved = a.saved

theorem emitText_text (st : St) (brk : Brk) (s : String) :
    itemsText (st.emitText brk s).items =
      itemsText st.items ++ (if replaced st.opens then "" else s) := by
  unfold St.emitText
  by_cases hr : replaced st.opens = true
  · simp [hr]
  · by_cases he : s.isEmpty = true
    · have : s = "" := by simpa using he
      subst this; simp
    · simp [hr, he, itemsText_push_text]

theorem emitText_keeps (st : St) (brk : Brk) (s : String) : Keeps st (st.emitText brk s) := by
  unfold St.emitText Keeps
  split <;> simp

/-- The text a string's codes read as. -/
@[expose] public def codesText (codes : List PdfFont.Code) : String :=
  String.join (codes.map (·.text))

theorem showCode_step (ts : TextState) (st0 : St) (a : ShowAcc) (code : PdfFont.Code) (pre : String)
    (hk : Keeps st0 a.st)
    (ht : itemsText a.st.items ++ (if replaced st0.opens then "" else a.cur) =
      itemsText st0.items ++ (if replaced st0.opens then "" else pre)) :
    Keeps st0 (St.showCode ts a code).st ∧
      itemsText (St.showCode ts a code).st.items ++
          (if replaced st0.opens then "" else (St.showCode ts a code).cur) =
        itemsText st0.items ++ (if replaced st0.opens then "" else pre ++ code.text) := by
  obtain ⟨ho, hts, hargs, hsv⟩ := hk
  unfold St.showCode
  dsimp only
  generalize (!a.cur.isEmpty && _ != Brk.none) = sp
  have he := emitText_text a.st a.curBrk a.cur
  have hke := emitText_keeps a.st a.curBrk a.cur
  rw [ho] at he
  cases sp <;> cases hl : code.text.isEmpty <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp_all [Keeps] <;>
    (by_cases hr : replaced st0.opens = true <;> simp_all [String.append_assoc])
  all_goals rw [← String.append_assoc, ht, String.append_assoc]

theorem showCode_fold (ts : TextState) (st0 : St) (codes : List PdfFont.Code) :
    ∀ (a : ShowAcc) (pre : String), Keeps st0 a.st →
      itemsText a.st.items ++ (if replaced st0.opens then "" else a.cur) =
        itemsText st0.items ++ (if replaced st0.opens then "" else pre) →
      Keeps st0 (codes.foldl (St.showCode ts) a).st ∧
        itemsText (codes.foldl (St.showCode ts) a).st.items ++
            (if replaced st0.opens then "" else (codes.foldl (St.showCode ts) a).cur) =
          itemsText st0.items ++ (if replaced st0.opens then "" else pre ++ codesText codes) := by
  induction codes with
  | nil => intro a pre hk ht; simpa [codesText] using And.intro hk ht
  | cons c rest ih =>
    intro a pre hk ht
    obtain ⟨hk', ht'⟩ := showCode_step ts st0 a c pre hk ht
    have := ih _ (pre ++ c.text) hk' ht'
    simpa [codesText, String.append_assoc] using this

theorem Keeps.refl (st : St) : Keeps st st := ⟨rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {a b c : St} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- The text a string shows in the font in force: its codes' text, none where a span replaces it
or no font is set. -/
@[expose] public def shownText (st : St) (b : ByteArray) : String :=
  match st.ts.font with
  | none => ""
  | some f => if replaced st.opens then "" else codesText (f.codes? b).toList

theorem showBytes_text (st : St) (b : ByteArray) :
    Keeps st (st.showBytes b) ∧
      itemsText (st.showBytes b).items = itemsText st.items ++ shownText st b := by
  unfold St.showBytes shownText
  split
  · next hf => exact ⟨⟨rfl, rfl, rfl, rfl⟩, by simp [hf]⟩
  · next f hf =>
    dsimp only
    have h := showCode_fold st.ts st (f.codes? b).toList ⟨st, "", st.brk, none⟩ ""
      (Keeps.refl st) (by simp)
    rw [Array.foldl_toList] at h
    generalize (f.codes? b).foldl (St.showCode st.ts) ⟨st, "", st.brk, none⟩ = a at h ⊢
    obtain ⟨hk, ht⟩ := h
    split
    · next hr =>
      simp only [hr, ite_true, String.append_empty] at ht
      exact ⟨hk, by simp [ht, hf]⟩
    · next hr =>
      simp only [hr, Bool.false_eq_true, ite_false, String.empty_append] at ht
      have he := emitText_text a.st a.curBrk a.cur
      have hke := emitText_keeps a.st a.curBrk a.cur
      rw [hk.1] at he
      simp only [hr, Bool.false_eq_true, ite_false] at he
      refine ⟨hk.trans hke, ?_⟩
      simp only [he, ht, hf]

/-- The operators the text reading treats only as moving the pen or setting a spacing. -/
@[expose] public def quietOp (n : String) : Bool :=
  !(["q", "Q", "Tf", "Tj", "'", "\"", "TJ", "BMC", "BDC", "EMC", "Do"].contains n)

theorem op_quiet (res : Res) (st : St) (n : String) (h : quietOp n = true) :
    (st.op res n).items = st.items ∧ ((st.op res n).opens = st.opens ∧
      (st.op res n).ts.font = st.ts.font) ∧ (st.op res n).args = #[] := by
  simp only [quietOp, Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_any_beq,
    List.any_eq_false, List.mem_cons, List.mem_nil_iff, or_false, beq_iff_eq] at h
  unfold St.op
  split <;> simp_all [St.nextLine]

theorem showElem_text (st s : St) (o : Obj) (hs : Keeps st s) :
    Keeps st (s.showElem o) ∧ itemsText (s.showElem o).items =
      itemsText s.items ++ ((PdfContentLex.strBytes? o).map (shownText st)).getD "" := by
  have hsh : shownText s = shownText st := by
    funext b
    simp only [shownText, hs.1, hs.2.1]
  unfold St.showElem
  cases hb : PdfContentLex.strBytes? o with
  | some b =>
    obtain ⟨hk, ht⟩ := showBytes_text s b
    exact ⟨hs.trans hk, by simp [ht, hsh]⟩
  | none =>
    cases num? o with
    | some n => exact ⟨hs, by simp⟩
    | none => exact ⟨hs, by simp⟩

theorem showArray_text (st : St) (xs : Array Obj) :
    Keeps st (st.showArray xs) ∧
      itemsText (st.showArray xs).items =
        itemsText st.items ++ String.join (xs.toList.map fun o =>
          ((PdfContentLex.strBytes? o).map (shownText st)).getD "") := by
  unfold St.showArray
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List Obj) (s : St), Keeps st s →
      Keeps st (l.foldl St.showElem s) ∧ itemsText (l.foldl St.showElem s).items =
        itemsText s.items ++ String.join (l.map fun o =>
          ((PdfContentLex.strBytes? o).map (shownText st)).getD "") from
    h xs.toList st (Keeps.refl st)
  intro l
  induction l with
  | nil => intro s hs; exact ⟨hs, by simp⟩
  | cons o rest ih =>
    intro s hs
    rw [List.foldl_cons]
    obtain ⟨hk, ht⟩ := showElem_text st s o hs
    obtain ⟨hk', ht'⟩ := ih _ hk
    exact ⟨hk', by rw [ht', ht, List.map_cons, String.join_cons, String.append_assoc]⟩

/-- The tokens of one operator: its operands, then its name. -/
theorem tok_fold_op (res : Res) (st : St) (vals : List Obj) (n : String) :
    (vals.map Tok.val ++ [Tok.op n]).foldl (St.tok res) st =
      St.op res { st with args := st.args ++ vals.toArray } n := by
  rw [List.foldl_append]
  have : ∀ (s : St), (vals.map Tok.val).foldl (St.tok res) s = { s with args := s.args ++ vals.toArray } := by
    induction vals with
    | nil => intro s; simp
    | cons v rest ih =>
      intro s
      rw [List.map_cons, List.foldl_cons, ih]
      simp only [St.tok]
      congr 1
      apply Array.ext'
      simp
  rw [this]
  rfl

theorem op_Tf (res : Res) (st : St) (nm : String) (v : Obj) (h : st.args = #[.name nm, v]) :
    (st.op res "Tf").items = st.items ∧ (st.op res "Tf").opens = st.opens ∧
      (st.op res "Tf").ts.font = res.fonts.get? nm ∧ (st.op res "Tf").args = #[] := by
  unfold St.op
  simp only [h, arg]
  cases hf : res.fonts[nm]? <;> simp [hf]

theorem op_TJ (res : Res) (st : St) (xs : Array Obj) (h : st.args = #[.arr xs]) :
    st.op res "TJ" = ({ st with args := #[] } : St).showArray xs := by
  unfold St.op
  simp [h, arg]

theorem op_BMC (res : Res) (st : St) (tag : String) (h : st.args = #[.name tag]) :
    (st.op res "BMC").items = st.items ∧
      (st.op res "BMC").opens = ⟨openMark (markOf st.opens) tag none, none⟩ :: st.opens ∧
      (st.op res "BMC").ts.font = st.ts.font ∧ (st.op res "BMC").args = #[] := by
  unfold St.op
  simp [h, arg]

theorem op_BDC (res : Res) (st : St) (tag : String) (es : Array (String × Obj))
    (h : st.args = #[.name tag, .dict es]) :
    (st.op res "BDC").items = st.items ∧
      (st.op res "BDC").opens =
        ⟨openMark (markOf st.opens) tag (some (.dict es)), actualOf (some (.dict es))⟩ :: st.opens ∧
      (st.op res "BDC").ts.font = st.ts.font ∧ (st.op res "BDC").args = #[] := by
  unfold St.op
  simp [h, arg]

theorem op_EMC (res : Res) (st : St) (o : Open) (rest : List Open) (h : st.opens = o :: rest) :
    itemsText (st.op res "EMC").items =
        itemsText st.items ++ (if replaced rest then "" else o.actual.getD "") ∧
      (st.op res "EMC").opens = rest ∧ (st.op res "EMC").ts.font = st.ts.font ∧
      (st.op res "EMC").args = #[] := by
  unfold St.op
  simp only [h]
  cases ha : o.actual with
  | none => simp
  | some t =>
    simp only []
    by_cases hr : replaced rest = true
    · simp [hr]
    · by_cases he : t.isEmpty = true
      · have : t = "" := by simpa using he
        subst this; simp [hr]
      · simp [hr, he, itemsText_push_text]

/-! ### The reading of the writer's text operators -/

/-- The reading agrees with the model: no operand pending, the font the model's resource names,
which is loaded, and whether a span replaces the text. -/
def Agrees (res : Res) (st : St) (k : Option Nat) (inSpan : Bool) : Prop :=
  st.args = #[] ∧ st.ts.font = k.bind (fun r => res.fonts.get? s!"F{r + 1}") ∧
    (∀ r, k = some r → (res.fonts.get? s!"F{r + 1}").isSome) ∧ replaced st.opens = inSpan

/-- Each font resource reads a hex string of glyph ids as their text through `T`. -/
public def FontReads (res : Res) (T : Nat → Nat → String) : Prop :=
  ∀ r f, res.fonts.get? s!"F{r + 1}" = some f → ∀ gs,
    ((PdfContentLex.strBytes? (gidStr gs)).map fun b => codesText (f.codes? b).toList) =
      some (String.join (gs.map (T r)))

theorem join_empty {α : Type} (l : List α) : String.join (l.map fun _ => "") = "" := by
  induction l with
  | nil => simp
  | cons _ rest ih => simp [ih]

theorem strBytes_int (n : Int) : PdfContentLex.strBytes? (.int n) = none := by
  simp [PdfContentLex.strBytes?]

theorem kernedObjs_text (g : Obj → String) (hT : ∀ gs, g (gidStr gs) = String.join (gs.map T'))
    (hi : ∀ n : Int, g (.int n) = "") :
    ∀ (l : List (Nat × Int)) (cur : List Nat),
      String.join ((kernedObjs l cur).map g) = String.join ((cur ++ l.map (·.1)).map T')
  | [], cur => by simp [kernedObjs, hT]
  | (gi, n) :: rest, cur => by
    unfold kernedObjs
    split
    · simp only [List.map_cons, String.join_cons, hT, hi, String.empty_append]
      rw [kernedObjs_text g hT hi rest [gi]]
      simp [List.map_append, String.join_append]
    · rw [kernedObjs_text g hT hi rest (cur ++ [gi])]
      simp [List.append_assoc]

theorem items_text (g : Obj → String) (T' : Nat → String) (hT : ∀ gs, g (gidStr gs) = String.join (gs.map T'))
    (hi : ∀ n : Int, g (.int n) = "") (items : List TextItem) :
    String.join ((items.flatMap TextItem.objs).map g) =
      String.join ((items.flatMap TextItem.gids).map T') := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, String.join_append,
      String.join_append, ih]
    congr 1
    cases it with
    | glyphs gids => simp [TextItem.objs, TextItem.gids, hT]
    | kerned gids nums =>
      simp only [TextItem.objs, TextItem.gids]
      rw [kernedObjs_text g hT hi, List.nil_append]
      simp [List.map_map, Function.comp_def]
    | adjust d => simp [TextItem.objs, TextItem.gids, hi]

theorem read_quiet (res : Res) (st : St) (vals : List Obj) (n : String) (h : quietOp n = true)
    {k : Option Nat} {inSpan : Bool} (ha : Agrees res st k inSpan) :
    let st' := (vals.map Tok.val ++ [Tok.op n]).foldl (St.tok res) st
    Agrees res st' k inSpan ∧ st'.opens = st.opens ∧ itemsText st'.items = itemsText st.items := by
  intro st'
  have e : st' = St.op res { st with args := st.args ++ vals.toArray } n := tok_fold_op res st vals n
  obtain ⟨hi, ⟨ho, hf⟩, hargs⟩ := op_quiet res { st with args := st.args ++ vals.toArray } n h
  rw [e]
  refine ⟨⟨hargs, ?_, ha.2.2.1, ?_⟩, ho, by rw [hi]⟩
  · rw [hf]; exact ha.2.1
  · rw [ho]; exact ha.2.2.2

/-- Several quiet operators, each after its operands. -/
theorem read_quiets (res : Res) (st : St) (ops : List (List Obj × String))
    (h : ∀ o ∈ ops, quietOp o.2 = true) {k : Option Nat} {inSpan : Bool} (ha : Agrees res st k inSpan) :
    let st' := (ops.flatMap fun (vs, n) => vs.map Tok.val ++ [Tok.op n]).foldl (St.tok res) st
    Agrees res st' k inSpan ∧ st'.opens = st.opens ∧ itemsText st'.items = itemsText st.items := by
  induction ops generalizing st with
  | nil => exact ⟨ha, rfl, rfl⟩
  | cons o rest ih =>
    obtain ⟨vs, n⟩ := o
    rw [List.flatMap_cons, List.foldl_append]
    obtain ⟨h1, h2, h3⟩ := read_quiet res st vs n (h (vs, n) (by simp)) ha
    obtain ⟨h4, h5, h6⟩ := ih _ (fun o' ho' => h o' (by simp [ho'])) h1
    exact ⟨h4, h5.trans h2, h6.trans h3⟩

theorem read_open (res : Res) (st : St) (t : MarkTag) {k : Option Nat} {inSpan : Bool}
    (ha : Agrees res st k inSpan) :
    let st' := (tagToks t).foldl (St.tok res) st
    st'.args = #[] ∧ st'.ts.font = st.ts.font ∧ st'.items = st.items ∧
      ∃ m, st'.opens = ⟨m, actualOf (tagProps t)⟩ :: st.opens := by
  intro st'
  have hargs := ha.1
  cases hp : tagProps t with
  | none =>
    have e : st' = St.op res { st with args := st.args ++ #[.name (tagName t)] } "BMC" := by
      show (tagToks t).foldl (St.tok res) st = _
      unfold tagToks
      rw [hp]
      exact tok_fold_op res st [.name (tagName t)] "BMC"
    obtain ⟨hi, ho, hf, ha'⟩ := op_BMC res { st with args := st.args ++ #[.name (tagName t)] } (tagName t)
      (by simp [hargs])
    rw [e]
    refine ⟨ha', hf, hi, openMark (markOf st.opens) (tagName t) none, ?_⟩
    rw [ho]
    simp [actualOf]
  | some p =>
    have hd : ∃ es, p = .dict es := by
      cases t with
      | artifact kk =>
        cases kk with
        | none => simp [tagProps] at hp
        | some kd => simp [tagProps] at hp; exact ⟨_, hp.symm⟩
      | content s m l => simp [tagProps] at hp; exact ⟨_, hp.symm⟩
      | span a => simp [tagProps] at hp; exact ⟨_, hp.symm⟩
    obtain ⟨es, rfl⟩ := hd
    have e : st' = St.op res { st with args := st.args ++ #[.name (tagName t), .dict es] } "BDC" := by
      show (tagToks t).foldl (St.tok res) st = _
      unfold tagToks
      rw [hp]
      exact tok_fold_op res st [.name (tagName t), .dict es] "BDC"
    obtain ⟨hi, ho, hf, ha'⟩ := op_BDC res { st with args := st.args ++ #[.name (tagName t), .dict es] }
      (tagName t) es (by simp [hargs])
    rw [e]
    exact ⟨ha', hf, hi, _, ho⟩

theorem actual_tagProps (t : MarkTag) :
    actualOf (tagProps t) = match t with
      | .span a => spanText? a
      | .artifact _ | .content _ _ _ => none := by
  cases t with
  | artifact kk => cases kk <;> simp [tagProps, actualOf, PdfRead.Obj.get?]
  | content s m l => simp [tagProps, actualOf, PdfRead.Obj.get?]
  | span a => rfl

mutual

theorem shown_inSpan : ∀ (res : Res) (T : Nat → Nat → String) (k : Option Nat) (o : TextOp),
    (TextOp.shown res T true k o).2 = ""
  | _, _, _, .scale _ | _, _, _, .move _ _ | _, _, _, .color _ | _, _, _, .font _ _ => rfl
  | _, _, _, .show _ => rfl
  | res, T, k, .marked (.span a) body => by
    simp only [TextOp.shown]
    cases spanText? a with
    | some s => rfl
    | none => exact shownList_inSpan res T k body.toList
  | res, T, k, .marked (.artifact _) body => shownList_inSpan res T k body.toList
  | res, T, k, .marked (.content _ _ _) body => shownList_inSpan res T k body.toList

theorem shownList_inSpan : ∀ (res : Res) (T : Nat → Nat → String) (k : Option Nat) (l : List TextOp),
    (TextOp.shownList res T true k l).2 = ""
  | _, _, _, [] => rfl
  | res, T, k, o :: rest => by
    simp only [TextOp.shownList, shown_inSpan res T k o, shownList_inSpan res T _ rest]
    rfl

end

mutual

/-- Reading a text operator's tokens shows the model's text and leaves the reading in agreement
with the model's font, its open sequences restored. -/
theorem toks_read (res : Res) (sp : Spell) (T : Nat → Nat → String)
    (hsp : ∀ c, ∀ o ∈ sp.color c, quietOp o.2 = true) (hT : FontReads res T) :
    ∀ (o : TextOp) (st : St) (k : Option Nat) (inSpan : Bool), Agrees res st k inSpan →
      Agrees res ((TextOp.toks sp o).foldl (St.tok res) st) (TextOp.shown res T inSpan k o).1 inSpan ∧
        ((TextOp.toks sp o).foldl (St.tok res) st).opens = st.opens ∧
        itemsText ((TextOp.toks sp o).foldl (St.tok res) st).items =
          itemsText st.items ++ (TextOp.shown res T inSpan k o).2
  | .scale p, st, k, inSpan, ha => by
    have := read_quiet res st [sp.scale p] "Tz" (by decide) ha
    simpa [TextOp.toks, TextOp.shown] using this
  | .move x y, st, k, inSpan, ha => by
    have := read_quiet res st [.int 1, .int 0, .int 0, .int 1, sp.len x, sp.len y] "Tm" (by decide) ha
    simpa [TextOp.toks, TextOp.shown] using this
  | .color c, st, k, inSpan, ha => by
    have := read_quiets res st (sp.color c) (hsp c) ha
    simpa [TextOp.toks, TextOp.shown] using this
  | .font r size, st, k, inSpan, ha => by
    have e : (TextOp.toks sp (.font r size)).foldl (St.tok res) st =
        St.op res { st with args := st.args ++ #[.name s!"F{r + 1}", sp.len size] } "Tf" :=
      tok_fold_op res st [.name s!"F{r + 1}", sp.len size] "Tf"
    obtain ⟨hi, ho, hf, hargs⟩ := op_Tf res { st with args := st.args ++ #[.name s!"F{r + 1}", sp.len size] }
      s!"F{r + 1}" (sp.len size) (by simp [ha.1])
    rw [e]
    have hsh : TextOp.shown res T inSpan k (.font r size) =
        ((res.fonts.get? s!"F{r + 1}").map fun _ => r, "") := rfl
    rw [hsh]
    refine ⟨⟨hargs, ?_, ?_, ?_⟩, ho, ?_⟩
    · rw [hf]
      cases hg : res.fonts.get? s!"F{r + 1}" with
      | none => rfl
      | some f => exact hg.symm
    · intro r' hr'
      cases hg : res.fonts.get? s!"F{r + 1}" with
      | none => rw [hg] at hr'; cases hr'
      | some f =>
        rw [hg] at hr'
        cases hr'
        rw [hg]; rfl
    · rw [ho]; exact ha.2.2.2
    · rw [hi, String.append_empty]
  | .show items, st, k, inSpan, ha => by
    have e : (TextOp.toks sp (.show items)).foldl (St.tok res) st =
        St.op res { st with args := st.args ++ #[.arr (items.toList.flatMap TextItem.objs).toArray] } "TJ" :=
      tok_fold_op res st [.arr (items.toList.flatMap TextItem.objs).toArray] "TJ"
    rw [e, op_TJ res _ (items.toList.flatMap TextItem.objs).toArray (by simp [ha.1])]
    generalize hs0 : ({ { st with args := st.args ++ #[Obj.arr (items.toList.flatMap TextItem.objs).toArray] }
      with args := #[] } : St) = s0
    have hs0a : s0.args = #[] := by rw [← hs0]
    have hs0f : s0.ts.font = st.ts.font := by rw [← hs0]
    have hs0o : s0.opens = st.opens := by rw [← hs0]
    have hs0i : s0.items = st.items := by rw [← hs0]
    obtain ⟨hk, ht⟩ := showArray_text s0 (items.toList.flatMap TextItem.objs).toArray
    refine ⟨⟨by rw [hk.2.2.1, hs0a], ?_, ha.2.2.1, ?_⟩, by rw [hk.1, hs0o], ?_⟩
    · simp only [TextOp.shown]; rw [hk.2.1, hs0f]; exact ha.2.1
    · rw [hk.1, hs0o]; exact ha.2.2.2
    · rw [ht, hs0i]
      simp only [TextOp.shown]
      congr 1
      rw [List.toList_toArray]
      have hrep : replaced s0.opens = inSpan := by rw [hs0o]; exact ha.2.2.2
      by_cases hin : inSpan = true
      · have hz : ∀ b, shownText s0 b = "" := by
          intro b; unfold shownText; split <;> simp [hrep, hin]
        simp only [hin, ite_true]
        rw [items_text _ (fun _ => "") (fun gs => by cases PdfContentLex.strBytes? (gidStr gs) <;> simp [hz, join_empty])
          (fun n => by simp [strBytes_int])]
        exact join_empty _
      · simp only [hin, Bool.false_eq_true, ite_false]
        cases hk' : k with
        | none =>
          have hz : ∀ b, shownText s0 b = "" := by
            intro b; simp only [shownText, hs0f, ha.2.1, hk', Option.bind_none]
          rw [items_text _ (fun _ => "") (fun gs => by cases PdfContentLex.strBytes? (gidStr gs) <;> simp [hz, join_empty])
            (fun n => by simp [strBytes_int])]
          exact join_empty _
        | some r =>
          obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (ha.2.2.1 r hk')
          have hsf : ∀ b, shownText s0 b = codesText (f.codes? b).toList := by
            intro b; unfold shownText; rw [hs0f, ha.2.1, hk']
            simp only [Option.bind_some, hf, hrep, hin, Bool.false_eq_true, ite_false]
          apply items_text _ (T r)
          · intro gs
            have := hT r f hf gs
            show ((PdfContentLex.strBytes? (gidStr gs)).map (shownText s0)).getD "" = _
            have hfun : shownText s0 = fun b => codesText (f.codes? b).toList := funext hsf
            rw [hfun, this]; rfl
          · intro n; simp [strBytes_int]
  | .marked tg body, st, k, inSpan, ha => by
    have hsplit : TextOp.toks sp (.marked tg body) =
        tagToks tg ++ TextOp.toksList sp body.toList ++ [Tok.op "EMC"] := rfl
    rw [hsplit, List.foldl_append, List.foldl_append]
    obtain ⟨h1a, h1f, h1i, m, h1o⟩ := read_open res st tg ha
    generalize (tagToks tg).foldl (St.tok res) st = st1 at h1a h1f h1i h1o
    have hag1 : Agrees res st1 k ((actualOf (tagProps tg)).isSome || inSpan) := by
      refine ⟨h1a, by rw [h1f]; exact ha.2.1, ha.2.2.1, ?_⟩
      rw [h1o]
      simp only [replaced, List.any_cons, ← ha.2.2.2]
    obtain ⟨h2a, h2o, h2t⟩ := toksList_read res sp T hsp hT body.toList st1 k _ hag1
    generalize (TextOp.toksList sp body.toList).foldl (St.tok res) st1 = st2 at h2a h2o h2t
    have he : List.foldl (St.tok res) st2 [Tok.op "EMC"] = St.op res st2 "EMC" := rfl
    rw [he]
    obtain ⟨h3t, h3o, h3f, h3a⟩ := op_EMC res st2 ⟨m, actualOf (tagProps tg)⟩ st.opens (by rw [h2o, h1o])
    simp only at h3t
    rw [ha.2.2.2] at h3t
    have hshown : TextOp.shown res T inSpan k (.marked tg body) =
        if (actualOf (tagProps tg)).isSome then
          ((TextOp.shownList res T true k body.toList).1,
            if inSpan then "" else (actualOf (tagProps tg)).getD "")
        else TextOp.shownList res T inSpan k body.toList := by
      rw [actual_tagProps]
      cases tg with
      | span a =>
        simp only [TextOp.shown]
        cases spanText? a <;> simp
      | artifact kk => simp [TextOp.shown]
      | content s mc l => simp [TextOp.shown]
    rw [hshown]
    refine ⟨⟨h3a, ?_, ?_, ?_⟩, h3o, ?_⟩
    · rw [h3f]
      split
      · next hs => simp only [hs, Bool.true_or] at h2a; exact h2a.2.1
      · next hs => simp only [Bool.not_eq_true] at hs; simp only [hs, Bool.false_or] at h2a; exact h2a.2.1
    · split
      · next hs => simp only [hs, Bool.true_or] at h2a; exact h2a.2.2.1
      · next hs => simp only [Bool.not_eq_true] at hs; simp only [hs, Bool.false_or] at h2a; exact h2a.2.2.1
    · rw [h3o]; exact ha.2.2.2
    · rw [h3t, h2t, h1i]
      by_cases hs : (actualOf (tagProps tg)).isSome = true
      · rw [ite_eq_left hs]
        simp only [hs, Bool.true_or, shownList_inSpan, String.append_empty]
      · rw [ite_eq_right hs]
        have hnone : actualOf (tagProps tg) = none := by
          cases h : actualOf (tagProps tg) with
          | none => rfl
          | some _ => simp [h] at hs
        simp only [hnone, Option.isSome_none, Bool.false_or, Option.getD_none, ite_self,
          String.append_empty]

theorem toksList_read (res : Res) (sp : Spell) (T : Nat → Nat → String)
    (hsp : ∀ c, ∀ o ∈ sp.color c, quietOp o.2 = true) (hT : FontReads res T) :
    ∀ (l : List TextOp) (st : St) (k : Option Nat) (inSpan : Bool), Agrees res st k inSpan →
      Agrees res ((TextOp.toksList sp l).foldl (St.tok res) st) (TextOp.shownList res T inSpan k l).1 inSpan ∧
        ((TextOp.toksList sp l).foldl (St.tok res) st).opens = st.opens ∧
        itemsText ((TextOp.toksList sp l).foldl (St.tok res) st).items =
          itemsText st.items ++ (TextOp.shownList res T inSpan k l).2
  | [], st, k, inSpan, ha => by simp [TextOp.toksList, TextOp.shownList, ha]
  | o :: rest, st, k, inSpan, ha => by
    obtain ⟨ha1, ho1, ht1⟩ := toks_read res sp T hsp hT o st k inSpan ha
    obtain ⟨ha2, ho2, ht2⟩ := toksList_read res sp T hsp hT rest _ _ inSpan ha1
    simp only [TextOp.toksList, TextOp.shownList, List.foldl_append]
    exact ⟨ha2, ho2.trans ho1, by rw [ht2, ht1, String.append_assoc]⟩

end

theorem textString_hyphen :
    PdfRead.textString generatedHyphen = hexObj (Hex.digits true 4 0xFEFF ++ Hex.digits true 4 0xAD) := by
  have hfe : "FEFF" = Hex.digits true 4 0xFEFF := by decide
  have hu : PdfRead.utf16Hex (Char.ofNat 0xAD) = Hex.digits true 4 0xAD := by
    unfold PdfRead.utf16Hex
    rw [ite_eq_left (by decide)]
    rfl
  unfold PdfRead.textString PdfRead.textStringBytes generatedHyphen hexObj
  rw [ite_eq_right (by decide)]
  simp only [String.toList_singleton, List.map_cons, List.map_nil, String.join_cons, String.join_nil,
    String.append_empty, hu, ← hfe]

theorem strBytes_hyphen :
    PdfContentLex.strBytes? (PdfRead.textString generatedHyphen) = some ⟨#[0xFE, 0xFF, 0, 0xAD]⟩ := by
  rw [textString_hyphen, Pdf.strBytes_hexObj, String.toList_append, List.map_append, List.foldl_append,
    Pdf.hexStep_digits4, Pdf.hexStep_digits4]
  rfl

theorem textString?_hyphen : textString? ⟨#[0xFE, 0xFF, 0, 0xAD]⟩ = some generatedHyphen := by
  unfold textString?
  rw [ite_eq_left (by decide +kernel)]
  have hx : (⟨#[0xFE, 0xFF, 0, 0xAD]⟩ : ByteArray).extract 2 (⟨#[0xFE, 0xFF, 0, 0xAD]⟩ : ByteArray).size =
      ⟨#[0, 0xAD]⟩ := rfl
  rw [hx]
  unfold PdfFont.utf16
  rw [show (⟨#[0, 0xAD]⟩ : ByteArray).data.toList = [0, 0xAD] from rfl, PdfFont.utf16Into.eq_def]
  simp only []
  rw [PdfFont.utf16Into.eq_def]
  simp [PdfFont.unit16, generatedHyphen]

/-- A generated hyphen's span reads as a soft hyphen. -/
public theorem spanText_hyphen : spanText? generatedHyphen = some generatedHyphen := by
  unfold spanText? actualOf
  simp only [Option.bind_some, PdfRead.Obj.get?]
  simp [strBytes_hyphen, textString?_hyphen]

/-- The text a text object the writer spells reads as, its items' strings joined with their breaks
and marks set aside: each string the writer shows reads as its glyphs' text through `T` in the
font resource the last `Tf` set, a span's actual text standing for its glyphs, in operator order. -/
public theorem extract_text (res : Res) (sp : Spell) (T : Nat → Nat → String)
    (hsp : ∀ c, ∀ o ∈ sp.color c, quietOp o.2 = true) (hT : FontReads res T) (ops : Array TextOp) :
    itemsText (readToks res .unmarked
        ([Tok.op "BT"] ++ TextOp.toksList sp ops.toList ++ [Tok.op "ET"]).toArray).1 =
      (TextOp.shownList res T false none ops.toList).2 := by
  unfold readToks
  dsimp only
  rw [← Array.foldl_toList, List.toList_toArray, List.foldl_append, List.foldl_append]
  have h0 : Agrees res (St.init .unmarked Mat.id) none false := ⟨rfl, rfl, by simp, rfl⟩
  obtain ⟨h1, -, ht1⟩ := read_quiet res (St.init .unmarked Mat.id) [] "BT" (by decide) h0
  simp only [List.map_nil, List.nil_append] at h1 ht1
  obtain ⟨h2, -, ht2⟩ := toksList_read res sp T hsp hT ops.toList _ none false h1
  obtain ⟨-, -, ht3⟩ := read_quiet res _ [] "ET" (by decide) h2
  simp only [List.map_nil, List.nil_append] at ht3
  rw [ht3, ht2, ht1]
  simp [St.init, itemsText]

/-! ### Two-byte identity fonts -/

/-- Glyph ids as two bytes each, big-endian. -/
@[expose] public def gidBytes (gs : List Nat) : List UInt8 :=
  gs.flatMap fun g => [UInt8.ofNat (g / 256 % 256), UInt8.ofNat (g % 256)]

theorem gidHex_digits (g : Nat) : gidHex g = Hex.digits true 4 g := by
  apply String.toList_inj.mp
  rw [gidHex_toList]
  simp only [Hex.digits, String.toList_ofList, Pdf.digitList4]
  simp [Nat.div_div_eq_div_mul]

theorem hexStep_gids (gs : List Nat) (acc : ByteArray) :
    ((String.join (gs.map gidHex)).toList.map digitByte).foldl PdfContentLex.hexStep (acc, none) =
      (acc ++ ⟨(gidBytes gs).toArray⟩, none) := by
  induction gs generalizing acc with
  | nil =>
    simp only [List.map_nil, String.join_nil, String.toList_empty, List.foldl_nil, gidBytes,
      List.flatMap_nil, Prod.mk.injEq, and_true]
    apply ByteArray.ext
    simp
  | cons g rest ih =>
    rw [List.map_cons, String.join_cons, String.toList_append, List.map_append, List.foldl_append,
      gidHex_digits, hexStep_digits4, ih]
    congr 1
    apply ByteArray.ext
    simp [gidBytes, ByteArray.data_append, ByteArray.data_push]

theorem strBytes_gidStr (gs : List Nat) :
    PdfContentLex.strBytes? (gidStr gs) = some ⟨(gidBytes gs).toArray⟩ := by
  unfold gidStr
  rw [strBytes_hexObj, hexStep_gids]
  simp

theorem bytesValue_two (pre : List UInt8) (a b : UInt8) (rest : List UInt8) :
    PdfFont.bytesValue ⟨(pre ++ a :: b :: rest).toArray⟩ pre.length 2 = a.toNat * 256 + b.toNat := by
  unfold PdfFont.bytesValue
  rw [show List.range' pre.length 2 = [pre.length, pre.length + 1] from rfl]
  simp

theorem compositeCodes_identity (program : PdfFont.Program) (cids : Array (Nat × Nat × Nat))
    (gidOf : Option ByteArray) (cff : Bool) (widths : Std.HashMap Nat Rat) (dw : Rat)
    (text : Std.HashMap Nat String) :
    ∀ (gs : List Nat) (pre : List UInt8) (out : Array PdfFont.Code),
      PdfFont.Loaded.compositeCodes program #[(2, 0, 0xFFFF)] cids gidOf cff widths dw text
          ⟨(pre ++ gidBytes gs).toArray⟩ pre.length out =
        out ++ (gs.map fun g =>
          PdfFont.Loaded.compositeCode program cids gidOf cff widths dw text (g % 65536) 2).toArray
  | [], pre, out => by
    rw [PdfFont.Loaded.compositeCodes]
    simp [gidBytes, ByteArray.size]
  | g :: rest, pre, out => by
    have hs : (pre ++ gidBytes (g :: rest)) =
        pre ++ UInt8.ofNat (g / 256 % 256) :: UInt8.ofNat (g % 256) :: gidBytes rest := by
      simp [gidBytes]
    have hv := bytesValue_two pre (UInt8.ofNat (g / 256 % 256)) (UInt8.ofNat (g % 256)) (gidBytes rest)
    simp only [UInt8.toNat_ofNat'] at hv
    have hv' : (g / 256 % 256 % 256) * 256 + g % 256 % 256 = g % 65536 := by omega
    rw [hv'] at hv
    have hlen : PdfFont.codeLen #[(2, 0, 0xFFFF)]
        ⟨(pre ++ UInt8.ofNat (g / 256 % 256) :: UInt8.ofNat (g % 256) :: gidBytes rest).toArray⟩
        pre.length = 2 := by
      unfold PdfFont.codeLen
      rw [show List.range' 1 4 = [1, 2, 3, 4] from rfl]
      simp only [List.find?_cons, ByteArray.size, List.size_toArray, List.length_append,
        List.length_cons, hv]
      have : g % 65536 ≤ 65535 := by omega
      simp [this]
    rw [hs, PdfFont.Loaded.compositeCodes]
    have hlt : pre.length <
        (⟨(pre ++ UInt8.ofNat (g / 256 % 256) :: UInt8.ofNat (g % 256) :: gidBytes rest).toArray⟩ :
          ByteArray).size := by
      simp [ByteArray.size]
    rw [ite_eq_left hlt]
    dsimp only
    rw [hlen, hv]
    have ih := compositeCodes_identity program cids gidOf cff widths dw text rest
      (pre ++ [UInt8.ofNat (g / 256 % 256), UInt8.ofNat (g % 256)])
      (out.push (PdfFont.Loaded.compositeCode program cids gidOf cff widths dw text (g % 65536) 2))
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons, List.length_nil] at ih
    rw [show pre.length + 2 = pre.length + (0 + 1 + 1) by omega, ih]
    apply Array.ext'
    simp

/-- Fonts that read two-byte codes through the identity codespace, as a Type0 font under
`Identity-H` loads, read each glyph id as its ToUnicode text. -/
public theorem fontReads_identity (res : Res) (texts : Nat → Std.HashMap Nat String)
    (h : ∀ r f, res.fonts.get? s!"F{r + 1}" = some f → ∃ cids gidOf cff widths dw v,
      f.codes = .composite #[(2, 0, 0xFFFF)] cids gidOf cff widths dw (texts r) v) :
    FontReads res (fun r g => ((texts r).get? (g % 65536)).getD "") := by
  intro r f hf gs
  obtain ⟨cids, gidOf, cff, widths, dw, v, hc⟩ := h r f hf
  rw [strBytes_gidStr]
  simp only [Option.map_some, Option.some.injEq]
  unfold PdfFont.Loaded.codes?
  rw [hc]
  dsimp only
  have := compositeCodes_identity f.program cids gidOf cff widths dw (texts r) gs [] #[]
  simp only [List.nil_append, List.length_nil, Array.empty_append] at this
  rw [this]
  simp [codesText, PdfFont.Loaded.compositeCode, Function.comp_def]

/-- The text a text object the writer spells reads as, breaks and marks set aside, its fonts
two-byte identity composites: each shown glyph id's ToUnicode text in the font the last `Tf` set,
a span's actual text for its glyphs. -/
public theorem extract_text_identity (res : Res) (sp : Spell) (texts : Nat → Std.HashMap Nat String)
    (hsp : ∀ c, ∀ o ∈ sp.color c, quietOp o.2 = true)
    (h : ∀ r f, res.fonts.get? s!"F{r + 1}" = some f → ∃ cids gidOf cff widths dw v,
      f.codes = .composite #[(2, 0, 0xFFFF)] cids gidOf cff widths dw (texts r) v)
    (ops : Array TextOp) :
    itemsText (readToks res .unmarked
        ([Tok.op "BT"] ++ TextOp.toksList sp ops.toList ++ [Tok.op "ET"]).toArray).1 =
      (TextOp.shownList res (fun r g => ((texts r).get? (g % 65536)).getD "") false none ops.toList).2 :=
  extract_text res sp _ hsp (fontReads_identity res texts h) ops

end LeanTex.Core.PdfContent
