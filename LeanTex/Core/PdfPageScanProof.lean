module

public import LeanTex.Core.PdfContentScanProof
import all LeanTex.Core.PdfContentScanProof
import all LeanTex.Core.PdfGfxReadback
import all LeanTex.Core.PdfContent
import all LeanTex.Core.PdfContentLex
import all LeanTex.Core.PdfContentLexProof
import all LeanTex.Core.PdfContentText
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfNameProof
import LeanTex.Core.PdfLexProof

/-! A page's content stream, as the writer spells it, reads as the text its text objects show. -/

namespace LeanTex.Core.PdfContent

open LeanTex.Core LeanTex.Core.Pdf LeanTex.Core.Dim LeanTex.Core.PdfGfx LeanTex.Core.Gfx
open LeanTex.Core.PdfContentLex (Tok)
open LeanTex.Core.PdfRead (Obj)
open LeanTex.Core.PdfTextRead

/-! ### Names the writer numbers -/

theorem esc_num (p : String) (hne : p ≠ "") (hp : ∀ c ∈ p.toList, PdfLex.nameKeeps c = true) (r : Nat) :
    PdfLex.escapeName (p ++ toString r) = p ++ toString r := by
  apply escapeName_plain _ (fun h => hne (by
    have := congrArg String.toList h
    simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at this
    exact String.toList_inj.mp (by simpa using this.1)))
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hp c hc
  · exact digit_keeps c (toDigits_digits r c (by simpa [Nat.toString_eq_repr, Nat.toList_repr] using hc))

theorem num_spelled (p : String) (hne : p ≠ "") (hp : ∀ c ∈ p.toList, c.toNat < 256) (r : Nat) :
    Obj.NameSpelling (p ++ toString r) := by
  refine ⟨fun h => hne (by
    have := congrArg String.toList h
    simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at this
    exact String.toList_inj.mp (by simpa using this.1)), ?_⟩
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hp c hc
  · have := toDigits_digits r c (by simpa [Nat.toString_eq_repr, Nat.toList_repr] using hc)
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
    have := this.2
    simp [UInt32.le_iff_toNat_le] at this
    change c.toNat ≤ 57 at this
    omega

/-- A numbered resource's name word. -/
def resW (p : String) (r : Nat) : Word := nameW (p ++ toString r)

theorem resW_ok (p : String) (hne : p ≠ "") (hp : ∀ c ∈ p.toList, c.toNat < 256) (r : Nat) :
    WordOk (resW p r) := nameW_ok _ (num_spelled p hne hp r)

theorem resW_str (p : String) (hne : p ≠ "") (hk : ∀ c ∈ p.toList, PdfLex.nameKeeps c = true) (r : Nat) :
    (resW p r).str = "/" ++ p ++ toString r := by
  simp only [resW, nameW, valW, esc_num p hne hk r, String.append_assoc]

@[simp] theorem resW_P (r : Nat) : (resW "P" r).str = "/P" ++ toString r := resW_str _ (by decide) (by decide) r
@[simp] theorem resW_GS (r : Nat) : (resW "GS" r).str = "/GS" ++ toString r :=
  resW_str _ (by decide) (by decide) r
@[simp] theorem resW_Im (r : Nat) : (resW "Im" r).str = "/Im" ++ toString r :=
  resW_str _ (by decide) (by decide) r
@[simp] theorem resW_Ri (r : Nat) : (resW "Ri" r).str = "/Ri" ++ toString r :=
  resW_str _ (by decide) (by decide) r
@[simp] theorem resW_Fm (r : Nat) : (resW "Fm" r).str = "/Fm" ++ toString r :=
  resW_str _ (by decide) (by decide) r
@[simp] theorem resW_Sh (r : Nat) : (resW "Sh" r).str = "/Sh" ++ toString r :=
  resW_str _ (by decide) (by decide) r
@[simp] theorem resW_sep (p : String) (r : Nat) : (resW p r).sep = 32 := rfl
@[simp] theorem esc_pattern : PdfLex.escapeName "Pattern" = "Pattern" :=
  escapeName_plain _ (by decide) (by decide)

/-! ### Paint states as words -/

/-- A colour's stroke operators' words. -/
def colorWordsS (c : Ir.Color) : List Word :=
  match c.pdfModel with
  | some (.rgb r g b) => [numW r, numW g, numW b, opW "RG"]
  | some (.gray v) => [numW v, opW "G"]
  | some (.cmyk cy m y k) => [numW cy, numW m, numW y, numW k, opW "K"]
  | some (.separation i t) => [nameW i.resKey, opW "CS", ratW t.num t.den, opW "SCN"]
  | none =>
    match c.cmyk with
    | some (cy, m, y, k) => [milliW cy, milliW m, milliW y, milliW k, opW "K"]
    | none => colorWords c ++ [opW "RG"]

def paintFillW : PdfPaint → List Word
  | .solid c => colorWordsT c
  | .pattern r _ => [nameW "Pattern", opW "cs", resW "P" (r + 1), opW "scn"]

def paintStrokeW : PdfPaint → List Word
  | .solid c => colorWordsS c
  | .pattern r _ => [nameW "Pattern", opW "CS", resW "P" (r + 1), opW "SCN"]

def gsW : Option ExtG → List Word
  | some g => [resW "GS" (g.res + 1), opW "gs"]
  | none => []

def fillStW : Option PaintFill → List Word
  | some f => paintFillW f.paint
  | none => []

def strokeStW : Option PaintStroke → List Word
  | some k => paintStrokeW k.paint ++ [lenW k.width, opW "w"] ++ capWords k.cap ++ joinWords k.join ++
      miterWords k.miter ++ dashWords k.dash
  | none => []

theorem colorWordsT_sp (c : Ir.Color) : (c.pdfFill ++ " ").toList = wordsChars (colorWordsT c) := by
  rw [Ir.Color.pdfFill_eq]
  unfold colorWordsT
  cases h : c.pdfModel with
  | none =>
    cases h' : c.cmyk with
    | none =>
      simp only [colorWords, milliW, opW, wordsChars_cons, sep_space,
        String.toList_append, components_chars, List.append_assoc, List.cons_append]
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.r) = x
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.g) = y
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.b) = z
      simp
    | some q =>
      obtain ⟨cy, m, y, k⟩ := q
      simp [milliW, opW, String.toList_append]
  | some p =>
    cases p with
    | rgb r g b => simp [numW, valW, opW, String.toList_append]
    | gray v => simp [numW, valW, opW, String.toList_append]
    | cmyk a b d e => simp [numW, valW, opW, String.toList_append]
    | separation i t =>
      simp only [nameW, valW, ratW, opW, wordsChars_cons, wordsChars_nil, sep_space,
        String.toList_append, List.append_assoc]
      generalize PdfLex.escapeName i.resKey = e
      generalize Dim.ratString t.num t.den = q
      simp

theorem colorWordsS_sp (c : Ir.Color) : (c.pdfStroke ++ " ").toList = wordsChars (colorWordsS c) := by
  rw [Ir.Color.pdfStroke_eq]
  unfold colorWordsS
  cases h : c.pdfModel with
  | none =>
    cases h' : c.cmyk with
    | none =>
      simp only [colorWords, milliW, opW, wordsChars_cons, sep_space,
        String.toList_append, components_chars, List.append_assoc, List.cons_append]
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.r) = x
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.g) = y
      generalize Ir.Color.pdfMilli (Ir.Color.milli c.b) = z
      simp
    | some q =>
      obtain ⟨cy, m, y, k⟩ := q
      simp [milliW, opW, String.toList_append]
  | some p =>
    cases p with
    | rgb r g b => simp [numW, valW, opW, String.toList_append]
    | gray v => simp [numW, valW, opW, String.toList_append]
    | cmyk a b d e => simp [numW, valW, opW, String.toList_append]
    | separation i t =>
      simp only [nameW, valW, ratW, opW, wordsChars_cons, wordsChars_nil, sep_space,
        String.toList_append, List.append_assoc]
      generalize PdfLex.escapeName i.resKey = e
      generalize Dim.ratString t.num t.den = q
      simp

theorem paintFillW_sp (p : PdfPaint) : (pdfPaintFill p ++ " ").toList = wordsChars (paintFillW p) := by
  cases p with
  | solid c => exact colorWordsT_sp c
  | pattern r g =>
    simp only [pdfPaintFill, paintFillW, nameW, valW, opW, wordsChars_cons, wordsChars_nil, sep_space,
      esc_pattern, resW_P, String.toList_append, ts]
    generalize toString (r + 1) = a
    simp

theorem paintStrokeW_sp (p : PdfPaint) : (pdfPaintStroke p ++ " ").toList = wordsChars (paintStrokeW p) := by
  cases p with
  | solid c => exact colorWordsS_sp c
  | pattern r g =>
    simp only [pdfPaintStroke, paintStrokeW, nameW, valW, opW, wordsChars_cons, wordsChars_nil, sep_space,
      esc_pattern, resW_P, String.toList_append, ts]
    generalize toString (r + 1) = a
    simp

theorem gsW_chars (gs : Option ExtG) : (gsState gs).toList = wordsChars (gsW gs) := by
  cases gs with
  | none => rfl
  | some g =>
    simp only [gsState, gsW, opW, wordsChars_cons, wordsChars_nil, sep_space, resW_GS,
      String.toList_append, ts]
    generalize toString (g.res + 1) = a
    simp

theorem fillStW_chars (fl : Option PaintFill) : (fillState fl).toList = wordsChars (fillStW fl) := by
  cases fl with
  | none => rfl
  | some f => exact paintFillW_sp f.paint

theorem strokeStW_chars (st : Option PaintStroke) : (strokeState st).toList = wordsChars (strokeStW st) := by
  cases st with
  | none => rfl
  | some k =>
    rw [strokeState_some]
    simp only [String.toList_append, capS_chars, joinS_chars, miterS_chars, dashS_chars, strokeStW,
      wordsChars_append]
    have h := paintStrokeW_sp k.paint
    simp only [String.toList_append] at h
    simp only [ts, ← h]
    simp [lenW, opW, List.append_assoc]

/-! ### Content operators as words -/

theorem wordsChars_endLine : ∀ (ws : List Word), ws ≠ [] → (∀ w ∈ ws, w.sep = 32) →
    wordsChars (endLine ws) = (wordsChars ws).dropLast ++ ['\n']
  | [], h, _ => absurd rfl h
  | [w], _, hs => by
    have hw : w.sep = 32 := hs w (by simp)
    simp [endLine, Word.nl, wordsChars_cons, hw]
  | w :: u :: rest, _, hs => by
    have hw : w.sep = 32 := hs w (by simp)
    have ih := wordsChars_endLine (u :: rest) (by simp) (fun v hv => hs v (by simp [hv]))
    show wordsChars (w :: endLine (u :: rest)) = _
    rw [wordsChars_cons, wordsChars_cons (w := w), hw, sep_space, ih]
    have hne : wordsChars (u :: rest) ≠ [] := by simp [wordsChars_cons]
    rw [show w.str.toList ++ ' ' :: wordsChars (u :: rest) = (w.str.toList ++ [' ']) ++ wordsChars (u :: rest)
      by simp, List.dropLast_append_of_ne_nil hne]
    simp

theorem endLine_chars (ws : List Word) (cs : List Char) (hne : ws ≠ []) (hs : ∀ w ∈ ws, w.sep = 32)
    (h : wordsChars ws = cs ++ [' ']) : wordsChars (endLine ws) = cs ++ ['\n'] := by
  rw [wordsChars_endLine ws hne hs, h, List.dropLast_concat]

/-- A real operand the writer spells as a literal. -/
def realW (s : String) : Word := valW (.real s) s

/-- A one-line content operator's words, each followed by a space. -/
def lineWords : ContentOp → List Word
  | .fill c x y w h =>
    [opW "q"] ++ colorWordsT c ++ [lenW x, lenW y, lenW w, lenW h, opW "re", opW "f", opW "Q"]
  | .paint fl st gs segs =>
    [opW "q"] ++ gsW gs ++ fillStW fl ++ strokeStW st ++ segs.toList.flatMap pathWords ++
      [opW (paintOp fl st), opW "Q"]
  | .image x y w h r =>
    [opW "q", lenW w, natW 0, natW 0, lenW h, lenW x, lenW y, opW "cm", resW "Im" (r + 1), opW "Do",
     opW "Q"]
  | .imageMissing x y w h =>
    [opW "q", realW "0.62", realW "0.62", realW "0.66", opW "RG", realW "0.75", opW "w", lenW x, lenW y,
     lenW w, lenW h, opW "re", opW "S", opW "Q"]
  | .shade r _ => [resW "Sh" (r + 1), opW "sh"]
  | .outline fl st segs => segs.toList.flatMap pathWords ++ [opW (outlineOp fl st)]
  | .xobject m r kind _ =>
    [opW "q"] ++ (m.map cmWords).getD [] ++ xstateW kind ++ [xnameW r kind, opW "Do", opW "Q"]
  | .text _ | .marked _ _ | .group _ _ _ _ => []
where
  xstateW : XKind → List Word
    | .stamp fp sp gs =>
      let stroke := strokeStW sp
      gsW gs ++ (fp.map paintFillW).getD [] ++ stroke
    | .raster _ | .symbol | .group => []
  xnameW (r : Nat) : XKind → Word
    | .raster _ => resW "Ri" (r + 1)
    | .symbol | .group | .stamp _ _ _ => resW "Fm" (r + 1)

theorem lineWords_fill_chars (c : Ir.Color) (x y w h : Length) :
    ((ContentOp.fill c x y w h).render ++ " ").toList = wordsChars (lineWords (.fill c x y w h)) := by
  simp only [ContentOp.render, lineWords, wordsChars_append, ← colorWordsT_sp, String.toList_append, ts]
  simp [lenW, opW, List.append_assoc]

theorem lineWords_paint_chars (fl : Option PaintFill) (st : Option PaintStroke) (gs : Option ExtG)
    (segs : Array PathOp) :
    ((ContentOp.paint fl st gs segs).render ++ " ").toList = wordsChars (lineWords (.paint fl st gs segs)) := by
  simp only [ContentOp.render]
  rw [← Array.foldl_toList, foldl_append_join]
  simp only [String.toList_append, lineWords, wordsChars_append, gsW_chars, fillStW_chars, strokeStW_chars,
    segs_chars]
  simp [opW, List.append_assoc]

theorem lineWords_image_chars (x y w h : Length) (r : Nat) :
    ((ContentOp.image x y w h r).render ++ " ").toList = wordsChars (lineWords (.image x y w h r)) := by
  simp only [ContentOp.render, lineWords, String.toList_append, ts, wordsChars_cons, wordsChars_nil,
    resW_Im, resW_sep, sep_space, opW, lenW, natW]
  generalize toString (r + 1) = f
  simp

theorem lineWords_missing_chars (x y w h : Length) :
    ((ContentOp.imageMissing x y w h).render ++ " ").toList = wordsChars (lineWords (.imageMissing x y w h)) := by
  simp only [ContentOp.render, lineWords, String.toList_append, ts, wordsChars_cons, wordsChars_nil,
    opW, lenW, realW, valW]
  simp

theorem lineWords_shade_chars (r : Nat) (g : Gradient) :
    ((ContentOp.shade r g).render ++ " ").toList = wordsChars (lineWords (.shade r g)) := by
  simp only [ContentOp.render, lineWords, String.toList_append, ts, wordsChars_cons, wordsChars_nil,
    resW_Sh, resW_sep, sep_space]
  generalize toString (r + 1) = f
  simp [opW]

theorem lineWords_outline_chars (fl : Option Rule) (st : Bool) (segs : Array PathOp) :
    ((ContentOp.outline fl st segs).render ++ " ").toList = wordsChars (lineWords (.outline fl st segs)) := by
  simp only [ContentOp.render]
  rw [← Array.foldl_toList, foldl_append_join]
  simp only [String.toList_append, lineWords, wordsChars_append, segs_chars, String.empty_append]
  simp [opW]

theorem six_chars (a b c d e f : String) : (a.toList ++ ' ' :: (b.toList ++ ' ' :: (c.toList ++ ' ' ::
    (d.toList ++ ' ' :: (e.toList ++ ' ' :: (f.toList ++ ' ' :: ("cm".toList ++ [' ']))))))) =
    a.toList ++ " ".toList ++ b.toList ++ " ".toList ++ c.toList ++ " ".toList ++ d.toList ++ " ".toList ++
      e.toList ++ " ".toList ++ f.toList ++ " cm ".toList := by
  simp

theorem cmWords_chars (mm : Affine) : wordsChars (cmWords mm) = (mm.operands ++ " cm ").toList := by
  rw [operands_eq, ratDecimal_eq, ratDecimal_eq, ratDecimal_eq, ratDecimal_eq]
  simp only [cmWords, ratW, opW, wordsChars_cons, wordsChars_nil, sep_space, String.toList_append]
  exact six_chars _ _ _ _ _ _

theorem xstateW_chars (kind : XKind) : (xobjectState kind).toList = wordsChars (lineWords.xstateW kind) := by
  cases kind with
  | stamp fp sp gs =>
    simp only [xobjectState, lineWords.xstateW, String.toList_append, wordsChars_append, gsW_chars,
      strokeStW_chars]
    cases fp with
    | none => rfl
    | some p =>
      have h := paintFillW_sp p
      simp only [String.toList_append] at h
      simp [← h]
  | raster _ | symbol | group => rfl

theorem xo_none (S N : String) (cs : List Char) (h : cs = []) :
    "q".toList ++ ("" : String).toList ++ " ".toList ++ S.toList ++ N.toList ++ " Do Q".toList ++
      " ".toList = ("q".toList ++ [' ']) ++ cs ++ S.toList ++ (N.toList ++ " Do Q ".toList) := by
  subst h; simp

theorem xo_some (O S N : String) :
    "q".toList ++ (" " ++ O ++ " cm").toList ++ " ".toList ++ S.toList ++ N.toList ++ " Do Q".toList ++
      " ".toList = ("q".toList ++ [' ']) ++ (O ++ " cm ").toList ++ S.toList ++
        (N.toList ++ " Do Q ".toList) := by
  simp [String.toList_append]

theorem lineWords_xobject_chars (m : Option Affine) (r : Nat) (kind : XKind) (body : Array ContentOp) :
    ((ContentOp.xobject m r kind body).render ++ " ").toList =
      wordsChars (lineWords (.xobject m r kind body)) := by
  have hname : (xobjectName r kind).toList ++ " Do Q ".toList =
      wordsChars [lineWords.xnameW r kind, opW "Do", opW "Q"] := by
    cases kind <;> simp [xobjectName, lineWords.xnameW, opW, String.toList_append, ts]
  have hq : wordsChars [opW "q"] = "q".toList ++ [' '] := by simp [opW]
  simp only [ContentOp.render, lineWords, wordsChars_append, String.toList_append, ← xstateW_chars,
    ← hname, hq]
  cases m with
  | none => exact xo_none _ _ _ rfl
  | some mm =>
    simp only [Option.map_some, Option.getD_some, cmWords_chars]
    exact xo_some _ _ _

/-! ### Every word but a line's last is followed by a space -/

def AllSp (ws : List Word) : Prop := ∀ w ∈ ws, w.sep = 32

@[simp] theorem sep_opW (n : String) : (opW n).sep = 32 := rfl
@[simp] theorem sep_lenW (x : Length) : (lenW x).sep = 32 := rfl
@[simp] theorem sep_natW (n : Nat) : (natW n).sep = 32 := rfl
@[simp] theorem sep_milliW (v : Nat) : (milliW v).sep = 32 := rfl
@[simp] theorem sep_ratW (p q : Int) : (ratW p q).sep = 32 := rfl
@[simp] theorem sep_valW (o : Obj) (s : String) : (valW o s).sep = 32 := rfl
@[simp] theorem sep_nameW (n : String) : (nameW n).sep = 32 := rfl
@[simp] theorem sep_numW (s : String) : (numW s).sep = 32 := rfl
@[simp] theorem sep_realW (s : String) : (realW s).sep = 32 := rfl
@[simp] theorem sep_dashW (d : Array Length) : (dashW d).sep = 32 := rfl

theorem allSp_append {a b : List Word} (ha : AllSp a) (hb : AllSp b) : AllSp (a ++ b) := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact ha w h
  · exact hb w h

theorem allSp_flatMap {α : Type} (f : α → List Word) (h : ∀ x, AllSp (f x)) (l : List α) :
    AllSp (l.flatMap f) := by
  intro w hw
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hw
  exact h x w hx

theorem colorWordsT_sp' (c : Ir.Color) : AllSp (colorWordsT c) := by
  unfold colorWordsT
  split
  all_goals try split
  all_goals simp [AllSp, colorWords]

theorem colorWordsS_sp' (c : Ir.Color) : AllSp (colorWordsS c) := by
  unfold colorWordsS
  split
  all_goals try split
  all_goals simp [AllSp, colorWords]

theorem paintFillW_sp' (p : PdfPaint) : AllSp (paintFillW p) := by
  cases p with
  | solid c => exact colorWordsT_sp' c
  | pattern _ _ => simp [AllSp, paintFillW, resW]

theorem paintStrokeW_sp' (p : PdfPaint) : AllSp (paintStrokeW p) := by
  cases p with
  | solid c => exact colorWordsS_sp' c
  | pattern _ _ => simp [AllSp, paintStrokeW, resW]

theorem gsW_sp (gs : Option ExtG) : AllSp (gsW gs) := by
  cases gs <;> simp [AllSp, gsW, resW]

theorem strokeStW_sp (st : Option PaintStroke) : AllSp (strokeStW st) := by
  cases st with
  | none => simp [AllSp, strokeStW]
  | some k =>
    refine allSp_append (allSp_append (allSp_append (allSp_append (allSp_append (paintStrokeW_sp' _)
      (by simp [AllSp])) ?_) ?_) ?_) ?_
    · cases k.cap <;> simp [AllSp, capWords]
    · cases k.join <;> simp [AllSp, joinWords]
    · cases k.miter <;> simp [AllSp, miterWords]
    · rcases k.dash with _ | ⟨d, p⟩ <;> simp [AllSp, dashWords]

theorem fillStW_sp (fl : Option PaintFill) : AllSp (fillStW fl) := by
  cases fl with
  | none => simp [AllSp, fillStW]
  | some f => exact paintFillW_sp' f.paint

theorem pathWords_sp (p : PathOp) : AllSp (pathWords p) := pathWords_sep p

theorem cmWords_sp (m : Option Affine) : AllSp ((m.map cmWords).getD []) := by
  cases m <;> simp [AllSp, cmWords]

theorem lineWords_sp (o : ContentOp) : AllSp (lineWords o) := by
  cases o with
  | fill c x y w h =>
    exact allSp_append (allSp_append (by simp [AllSp]) (colorWordsT_sp' c)) (by simp [AllSp])
  | paint fl st gs segs =>
    exact allSp_append (allSp_append (allSp_append (allSp_append (allSp_append (by simp [AllSp])
      (gsW_sp gs)) (fillStW_sp fl)) (strokeStW_sp st)) (allSp_flatMap _ pathWords_sp _)) (by simp [AllSp])
  | image x y w h r => simp [AllSp, lineWords, resW]
  | imageMissing x y w h => simp [AllSp, lineWords]
  | shade r g => simp [AllSp, lineWords, resW]
  | outline fl st segs => exact allSp_append (allSp_flatMap _ pathWords_sp _) (by simp [AllSp])
  | xobject m r kind body =>
    refine allSp_append (allSp_append (allSp_append (by simp [AllSp]) (cmWords_sp m)) ?_) ?_
    · cases kind with
      | stamp fp sp gs =>
        refine allSp_append (allSp_append (gsW_sp gs) ?_) (strokeStW_sp sp)
        cases fp with
        | none => simp [AllSp]
        | some p => exact paintFillW_sp' p
      | raster _ | symbol | group => simp [AllSp, lineWords.xstateW]
    · cases kind <;> simp [AllSp, lineWords.xnameW, resW]
  | text _ | marked _ _ | group _ _ _ _ => simp [AllSp, lineWords]

/-! ### Saved states, marked sequences, and the stream -/

def gsStr : Option ExtG → String
  | some g => s!" /GS{g.res + 1} gs"
  | none => ""

theorem groupHeader_eqG (m : Option Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Rule)) :
    groupHeader m gs clips = "q" ++ cmStr m ++ gsStr gs ++ String.join (clips.toList.map clipStr) := by
  cases m <;> cases gs <;> rfl

theorem gsStr_chars (gs : Option ExtG) : (gsStr gs).toList = lead (gsW gs) := by
  cases gs with
  | none => rfl
  | some g => simp [gsStr, gsW, lead, opW, String.toList_append, ts]

/-- A saved state's header words: `q`, its matrix, its alphas, its clips. -/
def headerG (m : Option Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Rule)) : List Word :=
  opW "q" :: (((m.map cmWords).getD []) ++ gsW gs ++ clips.toList.flatMap clipWords)

theorem headerG_sp (m : Option Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Rule)) :
    AllSp (((m.map cmWords).getD []) ++ gsW gs ++ clips.toList.flatMap clipWords) := by
  refine allSp_append (allSp_append (cmWords_sp m) (gsW_sp gs)) ?_
  intro w hw
  have := headerWords_sep none clips w (by simpa using hw)
  exact this

theorem headerG_chars (m : Option Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Rule)) :
    (groupHeader m gs clips ++ "\n").toList = wordsChars (endLine (headerG m gs clips)) := by
  rw [headerG, ← lead_endLine (opW "q") _ rfl (headerG_sp m gs clips), groupHeader_eqG]
  simp only [String.toList_append, cmStr_chars, gsStr_chars, clips_chars, lead_append, opW]
  simp

mutual

/-- A content operator's words, each line ended. -/
def opWordsG : ContentOp → List Word
  | .text ops => objWords ops
  | .marked t body => endLine (tagWords t) ++ opWordsGList body.toList ++ [(opW "EMC").nl]
  | .group m gs clips body => endLine (headerG m gs clips) ++ opWordsGList body.toList ++ [(opW "Q").nl]
  | .fill c x y w h => endLine (lineWords (.fill c x y w h))
  | .paint fl st gs segs => endLine (lineWords (.paint fl st gs segs))
  | .image x y w h r => endLine (lineWords (.image x y w h r))
  | .imageMissing x y w h => endLine (lineWords (.imageMissing x y w h))
  | .shade r g => endLine (lineWords (.shade r g))
  | .outline fl st segs => endLine (lineWords (.outline fl st segs))
  | .xobject m r kind body => endLine (lineWords (.xobject m r kind body))

def opWordsGList : List ContentOp → List Word
  | [] => []
  | o :: rest =>
    let tail := opWordsGList rest
    opWordsG o ++ tail

end

theorem line_chars (o : ContentOp) (h : (o.render ++ " ").toList = wordsChars (lineWords o))
    (hne : lineWords o ≠ []) : (o.render ++ "\n").toList = wordsChars (endLine (lineWords o)) := by
  rw [endLine_chars (lineWords o) o.render.toList hne (lineWords_sp o) (by rw [← h, String.toList_append]; rfl),
    String.toList_append]
  rfl

mutual

theorem opWordsG_chars : ∀ o : ContentOp, (o.render ++ "\n").toList = wordsChars (opWordsG o)
  | .text ops => objWords_chars ops
  | .marked t body => by
    rw [ContentOp.render, renderLines_eq, opWordsG]
    simp only [String.toList_append, wordsChars_append, ← tagWords_chars, ← opWordsGList_chars body.toList]
    simp [opW, Word.nl, List.append_assoc]
  | .group m gs clips body => by
    rw [ContentOp.render, renderLines_eq, opWordsG]
    simp only [String.toList_append, wordsChars_append, ← headerG_chars, ← opWordsGList_chars body.toList]
    simp [opW, Word.nl, List.append_assoc]
  | .fill c x y w h => line_chars _ (lineWords_fill_chars c x y w h) (by simp [lineWords])
  | .paint fl st gs segs => line_chars _ (lineWords_paint_chars fl st gs segs) (by simp [lineWords])
  | .image x y w h r => line_chars _ (lineWords_image_chars x y w h r) (by simp [lineWords])
  | .imageMissing x y w h => line_chars _ (lineWords_missing_chars x y w h) (by simp [lineWords])
  | .shade r g => line_chars _ (lineWords_shade_chars r g) (by simp [lineWords])
  | .outline fl st segs => line_chars _ (lineWords_outline_chars fl st segs) (by simp [lineWords])
  | .xobject m r kind body => line_chars _ (lineWords_xobject_chars m r kind body) (by simp [lineWords])

theorem opWordsGList_chars : ∀ l : List ContentOp,
    (String.join (l.map fun o => o.render ++ "\n")).toList = wordsChars (opWordsGList l)
  | [] => by simp [String.join_nil, opWordsGList]
  | o :: rest => by
    rw [List.map_cons, String.join_cons, String.toList_append, opWordsG_chars o,
      opWordsGList_chars rest, opWordsGList, wordsChars_append]

end

/-! ### Every word reads back, and none runs into the next -/

/-- Words each reading back, read in order as the tokens they stand for, ending with an operator. -/
def Fine (ws : List Word) : Prop := (∀ w ∈ ws, WordOk w) ∧ Good ws

theorem fine_append {a b : List Word} (ha : Fine a) (hb : Fine b) : Fine (a ++ b) :=
  ⟨fun w hw => (List.mem_append.mp hw).elim (ha.1 w) (hb.1 w), good_append a b ha.2 hb.2⟩

theorem fine_endLine {ws : List Word} (h : Fine ws) : Fine (endLine ws) :=
  ⟨endLine_ok ws h.1, good_endLine ws h.2⟩

theorem fine_noR (ws : List Word) (hok : ∀ w ∈ ws, WordOk w)
    (hr : ∀ w ∈ ws, PdfContentLex.leadR w.tok = false) (hl : ∀ w, ws.getLast? = some w → ∃ n, w.tok = .op n) :
    Fine ws :=
  ⟨hok, spelled_of _ (fun t ht => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht; exact (hok w hw).tok)
    (fun t ht => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht; exact hr w hw), hl⟩

theorem fine_free (ws : List Word) (hok : ∀ w ∈ ws, WordOk w) (hf : ∀ w ∈ ws, FreeW w)
    (hl : ∀ w, ws.getLast? = some w → ∃ n, w.tok = .op n) : Fine ws :=
  ⟨hok, good_free' ws hok hf hl⟩

theorem fine_nil : Fine [] := ⟨by simp, good_nil⟩

theorem fine_op (n : String) (h : PdfContentLex.OpSpelled n) : Fine [opW n] :=
  ⟨by simp only [List.mem_singleton]; rintro w rfl; exact opW_ok n h, good_opW n h⟩

theorem free_numW (s : String) : FreeW (numW s) := by
  intro o h
  simp only [numW, valW, Tok.val.injEq] at h
  subst h
  unfold numObj PdfContentLex.numberObj
  split
  · rfl
  · cases s.toInt? <;> rfl

theorem realW_ok (s : String) (hs : Obj.RealSpelling s) : WordOk (realW s) := valW_real s hs

theorem colorWordsT_fine (c : Ir.Color) (h : ColorSpelled c) : Fine (colorWordsT c) := by
  refine fine_noR _ (colorWordsT_ok c h) ?_ ?_
  · unfold colorWordsT
    split
    all_goals try split
    all_goals simp [colorWords, numW, valW, nameW, ratW, milliW, opW, PdfContentLex.leadR]
  · unfold colorWordsT
    split
    all_goals try split
    all_goals simp [colorWords, opW]

theorem colorWordsS_fine (c : Ir.Color) (h : ColorSpelled c) : Fine (colorWordsS c) := by
  unfold ColorSpelled at h
  unfold colorWordsS
  split at h
  all_goals rename_i hm
  all_goals simp only [hm]
  · obtain ⟨h1, h2, h3⟩ := h
    refine fine_free _ ?_ (by simp [free_numW]) (by simp [opW])
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact numW_ok _ h1
    · exact numW_ok _ h2
    · exact numW_ok _ h3
    · exact opW_ok _ (by opspelled)
  · refine fine_free _ ?_ (by simp [free_numW]) (by simp [opW])
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact numW_ok _ h
    · exact opW_ok _ (by opspelled)
  · obtain ⟨h1, h2, h3, h4⟩ := h
    refine fine_free _ ?_ (by simp [free_numW]) (by simp [opW])
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact numW_ok _ h1
    · exact numW_ok _ h2
    · exact numW_ok _ h3
    · exact numW_ok _ h4
    · exact opW_ok _ (by opspelled)
  · refine fine_noR _ ?_ (by simp [nameW, valW, ratW, opW, PdfContentLex.leadR]) (by simp [opW])
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact nameW_ok _ (resKey_spelled _)
    · exact opW_ok _ (by opspelled)
    · exact ratW_ok _ _
    · exact opW_ok _ (by opspelled)
  · split at h
    all_goals rename_i hc
    all_goals simp only [hc]
    · obtain ⟨h1, h2, h3, h4⟩ := h
      refine fine_free _ ?_ (by simp) (by simp [opW])
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact milliW_ok _ h1
      · exact milliW_ok _ h2
      · exact milliW_ok _ h3
      · exact milliW_ok _ h4
      · exact opW_ok _ (by opspelled)
    · refine fine_free _ ?_ (by simp [colorWords]) (by simp [opW])
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact colorWords_ok c w hw
      · rw [List.mem_singleton.mp hw]; exact opW_ok _ (by opspelled)

/-- A paint whose colour the writer spells as operands that read back. -/
@[expose] public def PaintSpelled : PdfPaint → Prop
  | .solid c => ColorSpelled c
  | .pattern _ _ => True

mutual

/-- The content operators' colours and tags hold the writer's spellings. -/
@[expose] public def ContentOp.Spelled : ContentOp → Prop
  | .fill c _ _ _ _ => ColorSpelled c
  | .paint fl st _ _ => (∀ f ∈ fl, PaintSpelled f.paint) ∧ (∀ k ∈ st, PaintSpelled k.paint)
  | .text ops => TextOp.SpelledList ops.toList
  | .marked (.content s _ _) body => Obj.NameSpelling s ∧ ContentOp.SpelledList body.toList
  | .marked (.artifact _) body | .marked (.span _) body => ContentOp.SpelledList body.toList
  | .group _ _ _ body => ContentOp.SpelledList body.toList
  | .xobject _ _ (.stamp fp sp _) _ => (∀ p ∈ fp, PaintSpelled p) ∧ (∀ k ∈ sp, PaintSpelled k.paint)
  | .xobject _ _ (.raster _) _ | .xobject _ _ .symbol _ | .xobject _ _ .group _ => True
  | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .shade _ _ | .outline _ _ _ => True

@[expose] public def ContentOp.SpelledList : List ContentOp → Prop
  | [] => True
  | o :: rest => ContentOp.Spelled o ∧ ContentOp.SpelledList rest

end

theorem paintFillW_fine (p : PdfPaint) (h : PaintSpelled p) : Fine (paintFillW p) := by
  cases p with
  | solid c => exact colorWordsT_fine c h
  | pattern r g =>
    refine fine_noR _ ?_ (by simp [paintFillW, nameW, valW, resW, opW, PdfContentLex.leadR])
      (by simp [paintFillW, opW])
    intro w hw
    simp only [paintFillW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact nameW_ok _ ⟨by decide, by decide⟩
    · exact opW_ok _ (by opspelled)
    · exact resW_ok _ (by decide) (by decide) _
    · exact opW_ok _ (by opspelled)

theorem paintStrokeW_fine (p : PdfPaint) (h : PaintSpelled p) : Fine (paintStrokeW p) := by
  cases p with
  | solid c => exact colorWordsS_fine c h
  | pattern r g =>
    refine fine_noR _ ?_ (by simp [paintStrokeW, nameW, valW, resW, opW, PdfContentLex.leadR])
      (by simp [paintStrokeW, opW])
    intro w hw
    simp only [paintStrokeW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact nameW_ok _ ⟨by decide, by decide⟩
    · exact opW_ok _ (by opspelled)
    · exact resW_ok _ (by decide) (by decide) _
    · exact opW_ok _ (by opspelled)

theorem gsW_fine (gs : Option ExtG) : Fine (gsW gs) := by
  cases gs with
  | none => exact fine_nil
  | some g =>
    refine fine_noR _ ?_ (by simp [gsW, resW, nameW, valW, opW, PdfContentLex.leadR]) (by simp [gsW, opW])
    intro w hw
    simp only [gsW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact resW_ok _ (by decide) (by decide) _
    · exact opW_ok _ (by opspelled)

theorem fillStW_fine (fl : Option PaintFill) (h : ∀ f ∈ fl, PaintSpelled f.paint) : Fine (fillStW fl) := by
  cases fl with
  | none => exact fine_nil
  | some f => exact paintFillW_fine f.paint (h f rfl)

theorem strokeStW_fine (st : Option PaintStroke) (h : ∀ k ∈ st, PaintSpelled k.paint) :
    Fine (strokeStW st) := by
  cases st with
  | none => exact fine_nil
  | some k =>
    have hw : Fine [lenW k.width, opW "w"] := by
      refine fine_free _ ?_ (by simp) (by simp [opW])
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact lenW_ok _
      · exact opW_ok _ (by opspelled)
    have hc : Fine (capWords k.cap) := by
      cases k.cap with
      | none => exact fine_nil
      | some c =>
        refine fine_free _ ?_ (by simp [capWords]) (by simp [capWords, opW])
        intro w hw
        simp only [capWords, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact natW_ok _
        · exact opW_ok _ (by opspelled)
    have hj : Fine (joinWords k.join) := by
      cases k.join with
      | none => exact fine_nil
      | some c =>
        refine fine_free _ ?_ (by simp [joinWords]) (by simp [joinWords, opW])
        intro w hw
        simp only [joinWords, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact natW_ok _
        · exact opW_ok _ (by opspelled)
    have hm : Fine (miterWords k.miter) := by
      cases k.miter with
      | none => exact fine_nil
      | some r =>
        refine fine_free _ ?_ (by simp [miterWords]) (by simp [miterWords, opW])
        intro w hw
        simp only [miterWords, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact ratW_ok _ _
        · exact opW_ok _ (by opspelled)
    have hd : Fine (dashWords k.dash) := by
      rcases k.dash with _ | ⟨d, p⟩
      · exact fine_nil
      · refine fine_noR _ ?_ (by simp [dashWords, dashW, lenW, opW, PdfContentLex.leadR])
          (by simp [dashWords, opW])
        intro w hw
        simp only [dashWords, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact dashW_ok _
        · exact lenW_ok _
        · exact opW_ok _ (by opspelled)
    exact fine_append (fine_append (fine_append (fine_append (fine_append
      (paintStrokeW_fine k.paint (h k rfl)) hw) hc) hj) hm) hd

theorem segs_fine : ∀ l : List PathOp, Fine (l.flatMap pathWords)
  | [] => fine_nil
  | p :: rest => by
    rw [List.flatMap_cons]
    exact fine_append ⟨pathWords_ok p, good_pathWords p⟩ (segs_fine rest)

theorem cmWords_fine (m : Option Affine) : Fine ((m.map cmWords).getD []) := by
  cases m with
  | none => exact fine_nil
  | some mm =>
    refine fine_free _ ?_ (by simp [cmWords]) (by simp [cmWords, opW])
    intro w hw
    simp only [Option.map_some, Option.getD_some, cmWords, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ratW_ok _ _
    · exact ratW_ok _ _
    · exact ratW_ok _ _
    · exact ratW_ok _ _
    · exact ratW_ok _ _
    · exact ratW_ok _ _
    · exact opW_ok _ (by opspelled)

theorem ops_fine (ns : List String) (h : ∀ n ∈ ns, PdfContentLex.OpSpelled n) : Fine (ns.map opW) := by
  induction ns with
  | nil => exact fine_nil
  | cons n rest ih =>
    rw [List.map_cons, ← List.singleton_append]
    exact fine_append (fine_op n (h n (by simp))) (ih fun m hm => h m (by simp [hm]))

theorem free_fine (ws : List Word) (n : String) (hok : ∀ w ∈ ws, WordOk w) (hf : ∀ w ∈ ws, FreeW w)
    (hn : PdfContentLex.OpSpelled n) : Fine (ws ++ [opW n]) := by
  refine fine_free _ ?_ ?_ (by simp [opW])
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hok w hw
    · rw [List.mem_singleton.mp hw]; exact opW_ok n hn
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hf w hw
    · rw [List.mem_singleton.mp hw]; simp

theorem outlineOp_spelled (fl : Option Rule) (st : Bool) : PdfContentLex.OpSpelled (outlineOp fl st) := by
  rcases fl with _ | (_ | _) <;> cases st <;> simp only [outlineOp] <;> opspelled

theorem lineWords_fine (o : ContentOp) (h : ContentOp.Spelled o) : Fine (lineWords o) := by
  cases o with
  | fill c x y w h' =>
    have e : lineWords (.fill c x y w h') = [opW "q"] ++ colorWordsT c ++
        ([lenW x, lenW y, lenW w, lenW h'] ++ [opW "re"]) ++ ["f", "Q"].map opW := by simp [lineWords]
    rw [e]
    refine fine_append (fine_append (fine_append (fine_op _ (by opspelled)) (colorWordsT_fine c h))
      (free_fine _ _ ?_ (by simp) (by opspelled))) (ops_fine _ (by simp; constructor <;> opspelled))
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl) <;> exact lenW_ok _
  | paint fl st gs segs =>
    have e : lineWords (.paint fl st gs segs) = [opW "q"] ++ gsW gs ++ fillStW fl ++ strokeStW st ++
        segs.toList.flatMap pathWords ++ [paintOp fl st, "Q"].map opW := by simp [lineWords]
    rw [e]
    exact fine_append (fine_append (fine_append (fine_append (fine_append (fine_op _ (by opspelled))
      (gsW_fine gs)) (fillStW_fine fl h.1)) (strokeStW_fine st h.2)) (segs_fine _))
      (ops_fine _ (by simp; exact ⟨paintOp_spelled fl st, by opspelled⟩))
  | image x y w h' r =>
    have e : lineWords (.image x y w h' r) = [opW "q"] ++
        ([lenW w, natW 0, natW 0, lenW h', lenW x, lenW y] ++ [opW "cm"]) ++
        [resW "Im" (r + 1), opW "Do"] ++ [opW "Q"] := by simp [lineWords]
    rw [e]
    refine fine_append (fine_append (fine_append (fine_op _ (by opspelled))
      (free_fine _ _ ?_ (by simp) (by opspelled))) ?_) (fine_op _ (by opspelled))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals first | exact lenW_ok _ | exact natW_ok _
    · refine fine_noR _ ?_ (by simp [resW, nameW, valW, opW, PdfContentLex.leadR]) (by simp [opW])
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl)
      · exact resW_ok _ (by decide) (by decide) _
      · exact opW_ok _ (by opspelled)
  | imageMissing x y w h' =>
    have e : lineWords (.imageMissing x y w h') = [opW "q"] ++
        ([realW "0.62", realW "0.62", realW "0.66"] ++ [opW "RG"]) ++ ([realW "0.75"] ++ [opW "w"]) ++
        ([lenW x, lenW y, lenW w, lenW h'] ++ [opW "re"]) ++ ["S", "Q"].map opW := by simp [lineWords]
    rw [e]
    have hr : ∀ s, s ∈ ["0.62", "0.66", "0.75"] → Obj.RealSpelling s := by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    refine fine_append (fine_append (fine_append (fine_append (fine_op _ (by opspelled))
      (free_fine _ _ ?_ ?_ (by opspelled))) (free_fine _ _ ?_ ?_ (by opspelled)))
      (free_fine _ _ ?_ (by simp) (by opspelled))) (ops_fine _ (by simp; constructor <;> opspelled))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl) <;> exact realW_ok _ (hr _ (by simp))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl) <;> (intro o ho; simp only [realW, valW, Tok.val.injEq] at ho; subst ho; rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v rfl; exact realW_ok _ (hr _ (by simp))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v rfl; intro o ho; simp only [realW, valW, Tok.val.injEq] at ho; subst ho; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl) <;> exact lenW_ok _
  | shade r g =>
    refine fine_noR _ ?_ (by simp [lineWords, resW, nameW, valW, opW, PdfContentLex.leadR])
      (by simp [lineWords, opW])
    simp only [lineWords, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl)
    · exact resW_ok _ (by decide) (by decide) _
    · exact opW_ok _ (by opspelled)
  | outline fl st segs =>
    exact fine_append (segs_fine _) (fine_op _ (outlineOp_spelled fl st))
  | xobject m r kind body =>
    have e : lineWords (.xobject m r kind body) = [opW "q"] ++ (m.map cmWords).getD [] ++
        lineWords.xstateW kind ++ [lineWords.xnameW r kind, opW "Do"] ++ [opW "Q"] := by simp [lineWords]
    rw [e]
    have hs : Fine (lineWords.xstateW kind) := by
      cases kind with
      | stamp fp sp gs =>
        simp only [ContentOp.Spelled] at h
        refine fine_append (fine_append (gsW_fine gs) ?_) (strokeStW_fine sp h.2)
        cases fp with
        | none => exact fine_nil
        | some p => exact paintFillW_fine p (h.1 p rfl)
      | raster _ | symbol | group => exact fine_nil
    have hn : Fine [lineWords.xnameW r kind, opW "Do"] := by
      refine fine_noR _ ?_ ?_ (by simp [opW])
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl)
        · cases kind <;> exact resW_ok _ (by decide) (by decide) _
        · exact opW_ok _ (by opspelled)
      · cases kind <;> simp [lineWords.xnameW, resW, nameW, valW, opW, PdfContentLex.leadR]
    exact fine_append (fine_append (fine_append (fine_append (fine_op _ (by opspelled)) (cmWords_fine m)) hs)
      hn) (fine_op _ (by opspelled))
  | text _ | marked _ _ | group _ _ _ _ => exact fine_nil

theorem headerG_fine (m : Option Affine) (gs : Option ExtG) (clips : Array (Array PathOp × Rule)) :
    Fine (headerG m gs clips) := by
  rw [headerG, ← List.singleton_append]
  refine fine_append (fine_op "q" (by opspelled)) (fine_append (fine_append (cmWords_fine m) (gsW_fine gs)) ?_)
  have : ∀ l : List (Array PathOp × Rule), Fine (l.flatMap clipWords) := by
    intro l
    induction l with
    | nil => exact fine_nil
    | cons c rest ih =>
      rw [List.flatMap_cons]
      refine fine_append (fine_append (segs_fine _) ?_) ih
      obtain ⟨_, rule⟩ := c
      cases rule
      · exact ops_fine ["W", "n"] (by simp; constructor <;> opspelled)
      · exact ops_fine ["W*", "n"] (by simp; constructor <;> opspelled)
  exact this _

theorem tagWords_fine (t : MarkTag) (h : ∀ s m l, t = .content s m l → Obj.NameSpelling s) :
    Fine (tagWords t) := by
  refine fine_noR _ (tagWords_ok t h) ?_ ?_
  · cases t with
    | artifact k => cases k <;> simp [tagWords, nameW, valW, opW, PdfContentLex.leadR]
    | content s m l => simp [tagWords, nameW, valW, opW, PdfContentLex.leadR]
    | span a => simp [tagWords, nameW, valW, opW, PdfContentLex.leadR]
  · cases t with
    | artifact k => cases k <;> simp [tagWords, opW]
    | content s m l => simp [tagWords, opW]
    | span a => simp [tagWords, opW]

theorem objWords_fine (ops : Array TextOp) (h : TextOp.SpelledList ops.toList) : Fine (objWords ops) := by
  refine fine_noR _ (objWords_ok ops h) ?_ (by
    intro w hw
    simp only [objWords, List.getLast?_concat, Option.some.injEq] at hw
    subst hw
    exact ⟨"ET", rfl⟩)
  intro w hw
  have ht : w.tok ∈ (objWords ops).map (·.tok) := List.mem_map_of_mem hw
  rw [objWords_tok] at ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with (ht | ht) | ht
  · rw [ht]; decide
  · exact toksList_noR _ _ ht
  · rw [ht]; decide

mutual

theorem opWordsG_fine : ∀ o : ContentOp, ContentOp.Spelled o → Fine (opWordsG o)
  | .text ops, h => objWords_fine ops h
  | .marked t body, h => by
    have hb : ContentOp.SpelledList body.toList := by
      cases t <;> simp only [ContentOp.Spelled] at h <;> first | exact h | exact h.2
    have ht : ∀ s m l, t = .content s m l → Obj.NameSpelling s := by
      intro s m l he
      subst he
      exact h.1
    rw [opWordsG]
    exact fine_append (fine_append (fine_endLine (tagWords_fine t ht)) (opWordsGList_fine body.toList hb))
      (fine_endLine (fine_op _ (by opspelled)))
  | .group m gs clips body, h => by
    rw [opWordsG]
    exact fine_append (fine_append (fine_endLine (headerG_fine m gs clips)) (opWordsGList_fine body.toList h))
      (fine_endLine (fine_op _ (by opspelled)))
  | .fill c x y w h', h => fine_endLine (lineWords_fine _ h)
  | .paint fl st gs segs, h => fine_endLine (lineWords_fine _ h)
  | .image x y w h' r, h => fine_endLine (lineWords_fine _ h)
  | .imageMissing x y w h', h => fine_endLine (lineWords_fine _ h)
  | .shade r g, h => fine_endLine (lineWords_fine _ h)
  | .outline fl st segs, h => fine_endLine (lineWords_fine _ h)
  | .xobject m r kind body, h => fine_endLine (lineWords_fine _ h)

theorem opWordsGList_fine : ∀ l : List ContentOp, ContentOp.SpelledList l → Fine (opWordsGList l)
  | [], _ => fine_nil
  | o :: rest, h => by
    rw [opWordsGList]
    exact fine_append (opWordsG_fine o h.1) (opWordsGList_fine rest h.2)

end

/-! ### The page stream scans back -/

theorem endLine_last : ∀ (ws : List Word), ws ≠ [] → ∃ w, (endLine ws).getLast? = some w ∧ w.sep = 10
  | [], h => absurd rfl h
  | [w], _ => ⟨w.nl, rfl, rfl⟩
  | w :: u :: rest, _ => by
    obtain ⟨v, hv, hs⟩ := endLine_last (u :: rest) (by simp)
    refine ⟨v, ?_, hs⟩
    show (w :: endLine (u :: rest)).getLast? = some v
    rw [List.getLast?_cons, hv]
    rfl

theorem opWordsG_last (o : ContentOp) : ∃ w, (opWordsG o).getLast? = some w ∧ w.sep = 10 := by
  cases o with
  | text ops => exact ⟨(opW "ET").nl, by simp only [opWordsG, objWords, List.getLast?_concat], rfl⟩
  | marked t body => exact ⟨(opW "EMC").nl, by simp [opWordsG], rfl⟩
  | group m gs clips body => exact ⟨(opW "Q").nl, by simp [opWordsG], rfl⟩
  | fill c x y w h => exact endLine_last _ (by simp [lineWords])
  | paint fl st gs segs => exact endLine_last _ (by simp [lineWords])
  | image x y w h r => exact endLine_last _ (by simp [lineWords])
  | imageMissing x y w h => exact endLine_last _ (by simp [lineWords])
  | shade r g => exact endLine_last _ (by simp [lineWords])
  | outline fl st segs => exact endLine_last _ (by simp [lineWords])
  | xobject m r kind body => exact endLine_last _ (by simp [lineWords])

theorem opWordsGList_last : ∀ (l : List ContentOp), l ≠ [] →
    ∃ w, (opWordsGList l).getLast? = some w ∧ w.sep = 10
  | [], h => absurd rfl h
  | [o], _ => by
    obtain ⟨w, hw, hs⟩ := opWordsG_last o
    exact ⟨w, by simpa [opWordsGList] using hw, hs⟩
  | o :: u :: rest, _ => by
    obtain ⟨w, hw, hs⟩ := opWordsGList_last (u :: rest) (by simp)
    refine ⟨w, ?_, hs⟩
    rw [opWordsGList]
    simp only [List.getLast?_append, hw]
    rfl

theorem page_bytes (ops : Array ContentOp) (h : ContentOp.SpelledList ops.toList) :
    (render ops).toUTF8 = PdfContentLex.renderSep false ((opWordsGList ops.toList).map fun w => (w.tok, w.sep)) := by
  by_cases he : ops.toList = []
  · have he' : ops = #[] := Array.toList_inj.mp he
    subst he'
    rw [show render #[] = "" from rfl]
    have e : opWordsGList (#[] : Array ContentOp).toList = [] := rfl
    rw [e, List.map_nil, String.toUTF8_eq_toByteArray, String.toByteArray_empty]
    rfl
  · obtain ⟨w, hw, hs⟩ := opWordsGList_last ops.toList he
    have hne : (opWordsGList ops.toList).map (fun w => (w.tok, w.sep)) ≠ [] := by
      intro hn
      rw [List.map_eq_nil_iff] at hn
      rw [hn] at hw
      simp at hw
    have hlast : (((opWordsGList ops.toList).map fun w => (w.tok, w.sep)).getLast hne).2 = 10 := by
      have := List.getLast?_map (f := fun w : Word => (w.tok, w.sep)) (l := opWordsGList ops.toList)
      rw [hw, Option.map_some, List.getLast?_eq_some_getLast hne] at this
      simp only [Option.some.injEq] at this
      rw [this]
      exact hs
    have hc := render_nl_chars ops he
    rw [opWordsGList_chars ops.toList] at hc
    have hb : (render ops ++ "\n").toUTF8 = (wordsChars (opWordsGList ops.toList)).utf8Encode := by
      rw [toUTF8_chars, hc]
    rw [words_bytes _ (opWordsGList_fine ops.toList h).1, PdfContentLex.renderSep_true _ hne, hlast] at hb
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_append] at hb
    have hnl : "\n".toByteArray = ⟨#[10]⟩ := rfl
    rw [hnl, ← String.toUTF8_eq_toByteArray] at hb
    exact bytes_cancel _ _ _ hb

/-- The bytes the writer spells for a content stream, its colours and tags holding the writer's
spellings, scan back as its operators' words' tokens. -/
theorem scan_render_page (ops : Array ContentOp) (h : ContentOp.SpelledList ops.toList) :
    PdfContentLex.scan (render ops).toUTF8 = ((opWordsGList ops.toList).map (·.tok)).toArray := by
  rw [page_bytes ops h, PdfContentLex.scan_renderSep_exact]
  · simp [List.map_map]
  · rw [List.map_map]
    exact (opWordsGList_fine ops.toList h).2.1
  · intro t ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    rcases ((opWordsGList_fine ops.toList h).1 w hw).sep with hs | hs <;> simp [hs] <;> decide

/-! ### The reading of a content stream -/

theorem op_saved (res : Res) (st : PdfTextRead.St) (n : String) (hq : n ≠ "q") (hQ : n ≠ "Q") :
    (st.op res n).saved = st.saved := by
  unfold PdfTextRead.St.op
  dsimp only
  split
  all_goals first
    | (exfalso; contradiction)
    | rfl
    | (split <;> rfl)
    | (split <;> (try split) <;> rfl)
    | (split <;> (try split) <;> (try split) <;> (try split) <;> rfl)
    | (split
       · exact (showBytes_text _ _).1.2.2.2
       · rfl)
    | (split
       · exact (showArray_text _ _).1.2.2.2
       · rfl)

theorem op_args (res : Res) (st : PdfTextRead.St) (n : String) : (st.op res n).args = #[] := by
  unfold PdfTextRead.St.op
  dsimp only
  split
  all_goals first
    | rfl
    | (split <;> rfl)
    | (split <;> (try split) <;> rfl)
    | (split <;> (try split) <;> (try split) <;> (try split) <;> rfl)
    | (split
       · exact (showBytes_text _ _).1.2.2.1
       · rfl)
    | (split
       · exact (showArray_text _ _).1.2.2.1
       · rfl)

theorem op_q (res : Res) (st : PdfTextRead.St) :
    st.op res "q" = { st with args := #[], saved := (st.ts, st.ctm) :: st.saved } := by
  unfold PdfTextRead.St.op
  rfl

theorem op_Q (res : Res) (st : PdfTextRead.St) (t : TextState) (m : Mat) (rest : List (TextState × Mat))
    (h : st.saved = (t, m) :: rest) :
    st.op res "Q" = { st with args := #[], ts := t, ctm := m, saved := rest } := by
  unfold PdfTextRead.St.op
  simp [h]

theorem op_Do (res : Res) (st : PdfTextRead.St) :
    itemsText (st.op res "Do").items = itemsText st.items ∧ (st.op res "Do").opens = st.opens ∧
      (st.op res "Do").ts.font = st.ts.font ∧ (st.op res "Do").saved = st.saved := by
  unfold PdfTextRead.St.op
  dsimp only
  split
  all_goals first
    | (exfalso; contradiction)
    | (split
       · split
         · simp
         · simp only [itemsText, Array.toList_push, List.filterMap_append, String.join_append]
           refine ⟨?_, trivial, trivial, trivial⟩
           rw [List.filterMap_cons_none rfl, List.filterMap_nil, String.join_nil, String.append_empty]
       · simp)

/-- Tokens whose operators the text reading passes over: quiet ones and `Do`. -/
def Passes (l : List Tok) : Prop := ∀ n, Tok.op n ∈ l → quietOp n = true ∨ n = "Do"

theorem walk : ∀ (l : List Tok) (st : PdfTextRead.St), Passes l →
    (l.foldl (PdfTextRead.St.tok res) st).ts.font = st.ts.font ∧
      (l.foldl (PdfTextRead.St.tok res) st).opens = st.opens ∧
      (l.foldl (PdfTextRead.St.tok res) st).saved = st.saved ∧
      itemsText (l.foldl (PdfTextRead.St.tok res) st).items = itemsText st.items
  | [], st, _ => ⟨rfl, rfl, rfl, rfl⟩
  | t :: rest, st, h => by
    rw [List.foldl_cons]
    have h1 : (PdfTextRead.St.tok res st t).ts.font = st.ts.font ∧
        (PdfTextRead.St.tok res st t).opens = st.opens ∧ (PdfTextRead.St.tok res st t).saved = st.saved ∧
        itemsText (PdfTextRead.St.tok res st t).items = itemsText st.items := by
      cases t with
      | val o => exact ⟨rfl, rfl, rfl, rfl⟩
      | inline d b => exact ⟨rfl, rfl, rfl, rfl⟩
      | op n =>
        rcases h n (by simp) with hq | rfl
        · obtain ⟨hi, ⟨ho, hf⟩, -⟩ := op_quiet res st n hq
          have hq' : n ≠ "q" := by intro e; subst e; simp [quietOp] at hq
          have hQ' : n ≠ "Q" := by intro e; subst e; simp [quietOp] at hq
          exact ⟨hf, ho, op_saved res st n hq' hQ', by simp only [PdfTextRead.St.tok, hi]⟩
        · obtain ⟨hi, ho, hf, hs⟩ := op_Do res st
          exact ⟨hf, ho, hs, hi⟩
    obtain ⟨a, b, c, d⟩ := walk rest _ (fun n hn => h n (by simp [hn]))
    exact ⟨a.trans h1.1, b.trans h1.2.1, c.trans h1.2.2.1, d.trans h1.2.2.2⟩

theorem fold_args (l : List Tok) (st : PdfTextRead.St) (n : String) (h : l.getLast? = some (.op n)) :
    (l.foldl (PdfTextRead.St.tok res) st).args = #[] := by
  obtain ⟨init, rfl⟩ : ∃ init, l = init ++ [.op n] := List.getLast?_eq_some_iff.mp h
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact op_args res _ n

/-! ### What a content stream shows -/

mutual

/-- What a content operator shows from the font resource in force: a text object's text, a saved
state's body's text with the font restored after it, a span's actual text for its content, nothing
for a path, an image or a form. -/
@[expose] public def ContentOp.shown (res : Res) (T : Nat → Nat → String) (inSpan : Bool)
    (k : Option Nat) : ContentOp → Option Nat × String
  | .text ops => TextOp.shownList res T inSpan k ops.toList
  | .group _ _ _ body => (k, (ContentOp.shownList res T inSpan k body.toList).2)
  | .marked (.span a) body =>
    match spanText? a with
    | some s => ((ContentOp.shownList res T true k body.toList).1, if inSpan then "" else s)
    | none => ContentOp.shownList res T inSpan k body.toList
  | .marked (.artifact _) body | .marked (.content _ _ _) body =>
    ContentOp.shownList res T inSpan k body.toList
  | .fill _ _ _ _ _ | .paint _ _ _ _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => (k, "")

@[expose] public def ContentOp.shownList (res : Res) (T : Nat → Nat → String) (inSpan : Bool)
    (k : Option Nat) : List ContentOp → Option Nat × String
  | [] => (k, "")
  | o :: rest =>
    let r := ContentOp.shown res T inSpan k o
    let r' := ContentOp.shownList res T inSpan r.1 rest
    (r'.1, r.2 ++ r'.2)

end

def QW (ws : List Word) : Prop := Passes (ws.map (·.tok))

theorem qw_append {a b : List Word} (ha : QW a) (hb : QW b) : QW (a ++ b) := by
  intro n hn
  rw [List.map_append] at hn
  rcases List.mem_append.mp hn with h | h
  · exact ha n h
  · exact hb n h

theorem qw_flatMap {α : Type} (f : α → List Word) (h : ∀ x, QW (f x)) (l : List α) : QW (l.flatMap f) := by
  intro n hn
  rw [List.map_flatMap] at hn
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hn
  exact h x n hx

theorem qw_nil : QW [] := by intro n hn; simp at hn

theorem colorWordsT_qw (c : Ir.Color) : QW (colorWordsT c) := by
  unfold colorWordsT
  split
  all_goals try split
  all_goals simp [QW, Passes, colorWords, numW, valW, nameW, ratW, milliW, opW, quietOp]

theorem colorWordsS_qw (c : Ir.Color) : QW (colorWordsS c) := by
  unfold colorWordsS
  split
  all_goals try split
  all_goals simp [QW, Passes, colorWords, numW, valW, nameW, ratW, milliW, opW, quietOp]

theorem paintFillW_qw (p : PdfPaint) : QW (paintFillW p) := by
  cases p with
  | solid c => exact colorWordsT_qw c
  | pattern _ _ => simp [QW, Passes, paintFillW, nameW, valW, resW, opW, quietOp]

theorem paintStrokeW_qw (p : PdfPaint) : QW (paintStrokeW p) := by
  cases p with
  | solid c => exact colorWordsS_qw c
  | pattern _ _ => simp [QW, Passes, paintStrokeW, nameW, valW, resW, opW, quietOp]

theorem gsW_qw (gs : Option ExtG) : QW (gsW gs) := by
  cases gs <;> simp [QW, Passes, gsW, resW, nameW, valW, opW, quietOp]

theorem fillStW_qw (fl : Option PaintFill) : QW (fillStW fl) := by
  cases fl with
  | none => exact qw_nil
  | some f => exact paintFillW_qw f.paint

theorem strokeStW_qw (st : Option PaintStroke) : QW (strokeStW st) := by
  cases st with
  | none => exact qw_nil
  | some k =>
    refine qw_append (qw_append (qw_append (qw_append (qw_append (paintStrokeW_qw _)
      (by simp [QW, Passes, lenW, opW, quietOp])) ?_) ?_) ?_) ?_
    · cases k.cap <;> simp [QW, Passes, capWords, natW, opW, quietOp]
    · cases k.join <;> simp [QW, Passes, joinWords, natW, opW, quietOp]
    · cases k.miter <;> simp [QW, Passes, miterWords, ratW, opW, quietOp]
    · rcases k.dash with _ | ⟨d, p⟩ <;> simp [QW, Passes, dashWords, dashW, lenW, opW, quietOp]

theorem pathWords_qw (p : PathOp) : QW (pathWords p) := by
  cases p <;> simp [QW, Passes, pathWords, lenW, opW, quietOp]

theorem cmWords_qw (m : Option Affine) : QW ((m.map cmWords).getD []) := by
  cases m <;> simp [QW, Passes, cmWords, ratW, opW, quietOp]

theorem clipWords_qw (c : Array PathOp × Rule) : QW (clipWords c) := by
  obtain ⟨segs, rule⟩ := c
  refine qw_append (qw_flatMap _ pathWords_qw _) ?_
  cases rule <;> simp [QW, Passes, opW, quietOp]

/-! ### Reading the stream -/

/-- A saved state's reading: `q`, a header the reading passes over, a body, `Q` restores the font. -/
theorem read_wrap (res : Res) (hdr body : List Tok) (txt : String) (hp : Passes hdr)
    (hl : hdr = [] ∨ ∃ n, hdr.getLast? = some (.op n)) (st : PdfTextRead.St) (k : Option Nat) (i : Bool)
    (ha : Agrees res st k i)
    (hbody : ∀ st1 : PdfTextRead.St, Agrees res st1 k i → st1.saved = (st.ts, st.ctm) :: st.saved →
      (body.foldl (PdfTextRead.St.tok res) st1).opens = st1.opens ∧
      (body.foldl (PdfTextRead.St.tok res) st1).saved = st1.saved ∧
      itemsText (body.foldl (PdfTextRead.St.tok res) st1).items = itemsText st1.items ++ txt) :
    let st' := ([Tok.op "q"] ++ hdr ++ body ++ [Tok.op "Q"]).foldl (PdfTextRead.St.tok res) st
    Agrees res st' k i ∧ st'.opens = st.opens ∧ st'.saved = st.saved ∧
      itemsText st'.items = itemsText st.items ++ txt := by
  intro st'
  have e1 : [Tok.op "q"].foldl (PdfTextRead.St.tok res) st = st.op res "q" := rfl
  simp only [st', List.foldl_append, e1, op_q]
  generalize hs1 : ({ st with args := #[], saved := (st.ts, st.ctm) :: st.saved } : PdfTextRead.St) = s1
  have hs1f : s1.ts = st.ts := by rw [← hs1]
  have hs1o : s1.opens = st.opens := by rw [← hs1]
  have hs1s : s1.saved = (st.ts, st.ctm) :: st.saved := by rw [← hs1]
  have hs1i : s1.items = st.items := by rw [← hs1]
  have hs1a : s1.args = #[] := by rw [← hs1]
  obtain ⟨w1, w2, w3, w4⟩ := walk (res := res) hdr s1 hp
  generalize hs2 : hdr.foldl (PdfTextRead.St.tok res) s1 = s2 at w1 w2 w3 w4
  have hs2a : s2.args = #[] := by
    rcases hl with rfl | ⟨n, hn⟩
    · rw [← hs2]; exact hs1a
    · rw [← hs2]; exact fold_args hdr s1 n hn
  have hag2 : Agrees res s2 k i :=
    ⟨hs2a, by rw [w1, hs1f]; exact ha.2.1, ha.2.2.1, by rw [w2, hs1o]; exact ha.2.2.2⟩
  obtain ⟨b1, b2, b3⟩ := hbody s2 hag2 (by rw [w3, hs1s])
  generalize body.foldl (PdfTextRead.St.tok res) s2 = s3 at b1 b2 b3
  have e2 : [Tok.op "Q"].foldl (PdfTextRead.St.tok res) s3 = s3.op res "Q" := rfl
  rw [e2, op_Q res s3 st.ts st.ctm st.saved (by rw [b2, w3, hs1s])]
  refine ⟨⟨rfl, ha.2.1, ha.2.2.1, ?_⟩, ?_, rfl, ?_⟩
  · show replaced s3.opens = i
    rw [b1, w2, hs1o]; exact ha.2.2.2
  · show s3.opens = st.opens
    rw [b1, w2, hs1o]
  · show itemsText s3.items = _
    rw [b3, w4, hs1i]

/-- The operators a text object's operators spell. -/
def textOpNames : List String := ["Tz", "Tm", "Tf", "TJ", "BMC", "BDC", "EMC", "rg", "g", "k", "cs", "scn"]

theorem tagToks_names (t : MarkTag) : ∀ u ∈ tagToks t, ∀ n, u = .op n → n ∈ textOpNames := by
  cases t with
  | artifact k => cases k <;> simp [tagToks, tagProps, textOpNames]
  | content s m l => simp [tagToks, tagProps, textOpNames]
  | span a => simp [tagToks, tagProps, textOpNames]

mutual

theorem toks_names : ∀ o : TextOp, ∀ t ∈ TextOp.toks writerSpell o, ∀ n, t = .op n → n ∈ textOpNames
  | .scale _ => by simp [TextOp.toks, textOpNames]
  | .move _ _ => by simp [TextOp.toks, textOpNames]
  | .font _ _ => by simp [TextOp.toks, textOpNames]
  | .color c => by
    intro t ht n hn
    subst hn
    rw [TextOp.toks] at ht
    obtain ⟨o, ho, ht⟩ := List.mem_flatMap.mp ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨v, _, hv⟩ := List.mem_map.mp ht; cases hv
    · rw [List.mem_singleton] at ht
      cases ht
      rcases colorToks_ops c o ho with h | h | h | h | h <;> rw [h] <;> simp [textOpNames]
  | .show _ => by simp [TextOp.toks, textOpNames]
  | .marked tg body => by
    intro t ht n hn
    rw [TextOp.toks] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact tagToks_names tg t ht n hn
    · exact toksList_names body.toList t ht n hn
    · cases hn; simp [textOpNames]

theorem toksList_names : ∀ l : List TextOp, ∀ t ∈ TextOp.toksList writerSpell l, ∀ n, t = .op n →
    n ∈ textOpNames
  | [] => by simp [TextOp.toksList]
  | o :: rest => by
    intro t ht
    rw [TextOp.toksList] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact toks_names o t ht
    · exact toksList_names rest t ht

end

theorem fold_saved (res : Res) : ∀ (l : List Tok) (st : PdfTextRead.St),
    (∀ n, Tok.op n ∈ l → n ≠ "q" ∧ n ≠ "Q") → (l.foldl (PdfTextRead.St.tok res) st).saved = st.saved
  | [], _, _ => rfl
  | t :: rest, st, h => by
    rw [List.foldl_cons, fold_saved res rest _ (fun n hn => h n (by simp [hn]))]
    cases t with
    | val o => rfl
    | inline d b => rfl
    | op n => exact op_saved res st n (h n (by simp)).1 (h n (by simp)).2

theorem text_noQ (ops : List TextOp) : ∀ n, Tok.op n ∈ TextOp.toksList writerSpell ops → n ≠ "q" ∧ n ≠ "Q" := by
  intro n hn
  have := toksList_names ops _ hn n rfl
  simp only [textOpNames, List.mem_cons, List.not_mem_nil, or_false] at this
  constructor <;> intro e <;> subst e <;> simp at this

/-- What a reading keeps reading an operator's tokens: the agreement, the open sequences and the
saved states, with the operator's text after the items'. -/
def Reads (res : Res) (toks : List Tok) (st : PdfTextRead.St) (k' : Option Nat) (i : Bool) (txt : String) : Prop :=
  Agrees res (toks.foldl (PdfTextRead.St.tok res) st) k' i ∧
    (toks.foldl (PdfTextRead.St.tok res) st).opens = st.opens ∧
    (toks.foldl (PdfTextRead.St.tok res) st).saved = st.saved ∧
    itemsText (toks.foldl (PdfTextRead.St.tok res) st).items = itemsText st.items ++ txt

theorem read_flat (res : Res) (l : List Tok) (hp : Passes l) (hl : ∃ n, l.getLast? = some (.op n))
    (st : PdfTextRead.St) (k : Option Nat) (i : Bool) (ha : Agrees res st k i) : Reads res l st k i "" := by
  obtain ⟨n, hn⟩ := hl
  obtain ⟨w1, w2, w3, w4⟩ := walk (res := res) l st hp
  exact ⟨⟨fold_args l st n hn, by rw [w1]; exact ha.2.1, ha.2.2.1, by rw [w2]; exact ha.2.2.2⟩, w2, w3,
    by rw [w4, String.append_empty]⟩

theorem read_boxed (res : Res) (mid : List Tok) (hp : Passes mid) (hl : ∃ n, mid.getLast? = some (.op n))
    (st : PdfTextRead.St) (k : Option Nat) (i : Bool) (ha : Agrees res st k i) :
    Reads res ([Tok.op "q"] ++ mid ++ [Tok.op "Q"]) st k i "" := by
  have h := read_wrap res mid [] "" hp (Or.inr hl) st k i ha
    (fun st1 _ _ => ⟨rfl, rfl, by rw [String.append_empty]; rfl⟩)
  simp only [List.append_nil] at h
  exact h

theorem last_op_append (a : List Tok) (n : String) : ∃ m, (a ++ [Tok.op n]).getLast? = some (.op m) :=
  ⟨n, by simp⟩

theorem read_text (res : Res) (T : Nat → Nat → String) (hT : FontReads res T) (ops : Array TextOp)
    (st : PdfTextRead.St) (k : Option Nat) (i : Bool) (ha : Agrees res st k i) :
    Reads res ((objWords ops).map (·.tok)) st (TextOp.shownList res T i k ops.toList).1 i
      (TextOp.shownList res T i k ops.toList).2 := by
  rw [objWords_tok]
  unfold Reads
  rw [List.foldl_append, List.foldl_append]
  obtain ⟨h1, o1, t1⟩ := read_quiet res st [] "BT" (by decide) ha
  simp only [List.map_nil, List.nil_append] at h1 o1 t1
  have s1 : ([Tok.op "BT"].foldl (PdfTextRead.St.tok res) st).saved = st.saved :=
    op_saved res st "BT" (by decide) (by decide)
  generalize [Tok.op "BT"].foldl (PdfTextRead.St.tok res) st = st1 at h1 o1 t1 s1
  obtain ⟨h2, o2, t2⟩ := toksList_read res writerSpell T writerSpell_quiet hT ops.toList st1 k i h1
  have s2 := fold_saved res (TextOp.toksList writerSpell ops.toList) st1 (text_noQ ops.toList)
  generalize (TextOp.toksList writerSpell ops.toList).foldl (PdfTextRead.St.tok res) st1 = st2 at h2 o2 t2 s2
  obtain ⟨h3, o3, t3⟩ := read_quiet res st2 [] "ET" (by decide) h2
  simp only [List.map_nil, List.nil_append] at h3 o3 t3
  have s3 : ([Tok.op "ET"].foldl (PdfTextRead.St.tok res) st2).saved = st2.saved :=
    op_saved res st2 "ET" (by decide) (by decide)
  exact ⟨h3, by rw [o3, o2, o1], by rw [s3, s2, s1], by rw [t3, t2, t1]⟩

theorem read_boxedW (res : Res) (mid : List Word) (hq : QW mid)
    (hl : ∃ n, (mid.map (·.tok)).getLast? = some (.op n)) (st : PdfTextRead.St) (k : Option Nat) (i : Bool)
    (ha : Agrees res st k i) : Reads res (([opW "q"] ++ mid ++ [opW "Q"]).map (·.tok)) st k i "" := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  exact read_boxed res _ hq hl st k i ha

theorem paintOp_quiet (fl : Option PaintFill) (st : Option PaintStroke) : quietOp (paintOp fl st) = true := by
  rcases paintOp_cases fl st with h | h | h | h | h | h <;> rw [h] <;> decide

theorem outlineOp_quiet (fl : Option Rule) (st : Bool) : quietOp (outlineOp fl st) = true := by
  rcases fl with _ | (_ | _) <;> cases st <;> decide

theorem last_words (a : List Word) (w : Word) (n : String) (h : w.tok = .op n) :
    ∃ m, ((a ++ [w]).map (·.tok)).getLast? = some (.op m) := ⟨n, by simp [h]⟩

theorem read_line (res : Res) (o : ContentOp)
    (hl : ∀ ops, o ≠ .text ops) (hm : ∀ t b, o ≠ .marked t b) (hg : ∀ m gs c b, o ≠ .group m gs c b)
    (st : PdfTextRead.St) (k : Option Nat) (i : Bool) (ha : Agrees res st k i) :
    Reads res ((lineWords o).map (·.tok)) st k i "" := by
  cases o with
  | fill c x y w h =>
    have e : lineWords (.fill c x y w h) = [opW "q"] ++
        (colorWordsT c ++ [lenW x, lenW y, lenW w, lenW h, opW "re", opW "f"]) ++ [opW "Q"] := by
      simp [lineWords]
    rw [e]
    refine read_boxedW res _ (qw_append (colorWordsT_qw c) (by simp [QW, Passes, lenW, opW, quietOp]))
      ?_ st k i ha
    exact ⟨"f", by simp [opW]⟩
  | paint fl stk gs segs =>
    have e : lineWords (.paint fl stk gs segs) = [opW "q"] ++
        (gsW gs ++ fillStW fl ++ strokeStW stk ++ segs.toList.flatMap pathWords ++ [opW (paintOp fl stk)]) ++
          [opW "Q"] := by
      simp [lineWords]
    rw [e]
    refine read_boxedW res _ (qw_append (qw_append (qw_append (qw_append (gsW_qw gs) (fillStW_qw fl))
      (strokeStW_qw stk)) (qw_flatMap _ pathWords_qw _)) ?_) (last_words _ _ _ rfl) st k i ha
    intro n hn
    simp only [List.map_cons, List.map_nil, List.mem_singleton, opW, Tok.op.injEq] at hn
    subst hn
    exact Or.inl (paintOp_quiet fl stk)
  | image x y w h r =>
    have e : lineWords (.image x y w h r) = [opW "q"] ++
        [lenW w, natW 0, natW 0, lenW h, lenW x, lenW y, opW "cm", resW "Im" (r + 1), opW "Do"] ++
          [opW "Q"] := by
      simp [lineWords]
    rw [e]
    exact read_boxedW res _ (by simp [QW, Passes, lenW, natW, resW, nameW, valW, opW, quietOp])
      ⟨"Do", by simp [opW]⟩ st k i ha
  | imageMissing x y w h =>
    have e : lineWords (.imageMissing x y w h) = [opW "q"] ++
        [realW "0.62", realW "0.62", realW "0.66", opW "RG", realW "0.75", opW "w", lenW x, lenW y,
         lenW w, lenW h, opW "re", opW "S"] ++ [opW "Q"] := by
      simp [lineWords]
    rw [e]
    exact read_boxedW res _ (by simp [QW, Passes, lenW, realW, valW, opW, quietOp])
      ⟨"S", by simp [opW]⟩ st k i ha
  | xobject m r kind body =>
    have e : lineWords (.xobject m r kind body) = [opW "q"] ++
        ((m.map cmWords).getD [] ++ lineWords.xstateW kind ++ [lineWords.xnameW r kind, opW "Do"]) ++
          [opW "Q"] := by
      simp [lineWords]
    rw [e]
    have hx : QW (lineWords.xstateW kind) := by
      cases kind with
      | stamp fp sp gs =>
        refine qw_append (qw_append (gsW_qw gs) ?_) (strokeStW_qw sp)
        cases fp with
        | none => exact qw_nil
        | some p => exact paintFillW_qw p
      | raster _ | symbol | group => exact qw_nil
    refine read_boxedW res _ (qw_append (qw_append (cmWords_qw m) hx) ?_) ⟨"Do", by simp [opW]⟩ st k i ha
    cases kind <;> simp [QW, Passes, lineWords.xnameW, resW, nameW, valW, opW, quietOp]
  | shade r g =>
    exact read_flat res _ (by simp [Passes, lineWords, resW, nameW, valW, opW, quietOp])
      ⟨"sh", by simp [lineWords, opW]⟩ st k i ha
  | outline fl stk segs =>
    refine read_flat res _ ?_ (last_words _ _ _ rfl) st k i ha
    refine qw_append (qw_flatMap _ pathWords_qw _) ?_
    intro n hn
    simp only [List.map_cons, List.map_nil, List.mem_singleton, opW, Tok.op.injEq] at hn
    subst hn
    exact Or.inl (outlineOp_quiet fl stk)
  | text ops => exact absurd rfl (hl ops)
  | marked t b => exact absurd rfl (hm t b)
  | group m gs c b => exact absurd rfl (hg m gs c b)

mutual

theorem shown_inSpan' : ∀ (res : Res) (T : Nat → Nat → String) (k : Option Nat) (o : ContentOp),
    (ContentOp.shown res T true k o).2 = ""
  | res, T, k, .text ops => shownList_inSpan res T k ops.toList
  | res, T, k, .group _ _ _ body => shownList_inSpan' res T k body.toList
  | res, T, k, .marked (.span a) body => by
    simp only [ContentOp.shown]
    cases spanText? a with
    | some s => rfl
    | none => exact shownList_inSpan' res T k body.toList
  | res, T, k, .marked (.artifact _) body => shownList_inSpan' res T k body.toList
  | res, T, k, .marked (.content _ _ _) body => shownList_inSpan' res T k body.toList
  | _, _, _, .fill _ _ _ _ _ | _, _, _, .paint _ _ _ _ | _, _, _, .image _ _ _ _ _
  | _, _, _, .imageMissing _ _ _ _ | _, _, _, .shade _ _ | _, _, _, .outline _ _ _
  | _, _, _, .xobject _ _ _ _ => rfl

theorem shownList_inSpan' : ∀ (res : Res) (T : Nat → Nat → String) (k : Option Nat) (l : List ContentOp),
    (ContentOp.shownList res T true k l).2 = ""
  | _, _, _, [] => rfl
  | res, T, k, o :: rest => by
    simp only [ContentOp.shownList, shown_inSpan' res T k o, shownList_inSpan' res T _ rest]
    rfl

end

theorem reads_line (res : Res) (T : Nat → Nat → String) (o : ContentOp)
    (hl : ∀ ops, o ≠ .text ops) (hm : ∀ t b, o ≠ .marked t b) (hg : ∀ m gs c b, o ≠ .group m gs c b)
    (hs : ContentOp.shown res T i k o = (k, ""))
    (st : PdfTextRead.St) (ha : Agrees res st k i) (he : opWordsG o = endLine (lineWords o)) :
    Reads res ((opWordsG o).map (·.tok)) st (ContentOp.shown res T i k o).1 i (ContentOp.shown res T i k o).2 := by
  rw [he, endLine_tok, hs]
  exact read_line res o hl hm hg st k i ha

mutual

theorem read_op (res : Res) (T : Nat → Nat → String) (hT : FontReads res T) :
    ∀ (o : ContentOp) (st : PdfTextRead.St) (k : Option Nat) (i : Bool), Agrees res st k i →
      Reads res ((opWordsG o).map (·.tok)) st (ContentOp.shown res T i k o).1 i (ContentOp.shown res T i k o).2
  | .text ops, st, k, i, ha => by
    simp only [opWordsG, ContentOp.shown]
    exact read_text res T hT ops st k i ha
  | .group m gs clips body, st, k, i, ha => by
    have e : (opWordsG (.group m gs clips body)).map (·.tok) =
        [Tok.op "q"] ++ (((m.map cmWords).getD [] ++ gsW gs ++ clips.toList.flatMap clipWords).map (·.tok)) ++
          (opWordsGList body.toList).map (·.tok) ++ [Tok.op "Q"] := by
      simp [opWordsG, endLine_tok, headerG, opW, Word.nl]
    rw [e]
    simp only [ContentOp.shown]
    have hh : ((m.map cmWords).getD [] ++ gsW gs ++ clips.toList.flatMap clipWords).map (·.tok) = [] ∨
        ∃ n, (((m.map cmWords).getD [] ++ gsW gs ++ clips.toList.flatMap clipWords).map (·.tok)).getLast? =
          some (.op n) := by
      generalize hH : (m.map cmWords).getD [] ++ gsW gs ++ clips.toList.flatMap clipWords = H
      have hg := (headerG_fine m gs clips).2.2
      rw [headerG, hH] at hg
      cases H.eq_nil_or_concat with
      | inl h0 => left; rw [h0]; rfl
      | inr h1 =>
        obtain ⟨L, b, rfl⟩ := h1
        right
        obtain ⟨n, hn⟩ := hg b (by
          rw [List.concat_eq_append, ← List.cons_append, List.getLast?_concat])
        exact ⟨n, by simp [hn]⟩
    exact read_wrap res _ _ _ (qw_append (qw_append (cmWords_qw m) (gsW_qw gs)) (qw_flatMap _ clipWords_qw _))
      hh st k i ha (fun st1 h1 _ => by
        obtain ⟨-, a, b, c⟩ := read_ops res T hT body.toList st1 k i h1
        exact ⟨a, b, c⟩)
  | .marked tg body, st, k, i, ha => by
    have hsplit : (opWordsG (.marked tg body)).map (·.tok) =
        tagToks tg ++ (opWordsGList body.toList).map (·.tok) ++ [Tok.op "EMC"] := by
      simp [opWordsG, endLine_tok, tagWords_tok, opW, Word.nl]
    unfold Reads
    rw [hsplit, List.foldl_append, List.foldl_append]
    obtain ⟨h1a, h1f, h1i, mk, h1o⟩ := read_open res st tg ha
    have h1s : ((tagToks tg).foldl (PdfTextRead.St.tok res) st).saved = st.saved :=
      fold_saved res _ st (fun n hn => by
        have := tagToks_names tg _ hn n rfl
        simp only [textOpNames, List.mem_cons, List.not_mem_nil, or_false] at this
        constructor <;> intro e <;> subst e <;> simp at this)
    generalize (tagToks tg).foldl (PdfTextRead.St.tok res) st = st1 at h1a h1f h1i h1o h1s
    have hag1 : Agrees res st1 k ((actualOf (tagProps tg)).isSome || i) := by
      refine ⟨h1a, by rw [h1f]; exact ha.2.1, ha.2.2.1, ?_⟩
      rw [h1o]
      simp only [replaced, List.any_cons, ← ha.2.2.2]
    obtain ⟨h2a, h2o, h2s, h2t⟩ := read_ops res T hT body.toList st1 k _ hag1
    generalize ((opWordsGList body.toList).map (·.tok)).foldl (PdfTextRead.St.tok res) st1 = st2
      at h2a h2o h2s h2t
    have he : List.foldl (PdfTextRead.St.tok res) st2 [Tok.op "EMC"] = PdfTextRead.St.op res st2 "EMC" := rfl
    rw [he]
    obtain ⟨h3t, h3o, h3f, h3a⟩ := op_EMC res st2 ⟨mk, actualOf (tagProps tg)⟩ st.opens (by rw [h2o, h1o])
    have h3s := op_saved res st2 "EMC" (by decide) (by decide)
    simp only at h3t
    rw [ha.2.2.2] at h3t
    have hshown : ContentOp.shown res T i k (.marked tg body) =
        if (actualOf (tagProps tg)).isSome then
          ((ContentOp.shownList res T true k body.toList).1,
            if i then "" else (actualOf (tagProps tg)).getD "")
        else ContentOp.shownList res T i k body.toList := by
      rw [actual_tagProps]
      cases tg with
      | span a =>
        simp only [ContentOp.shown]
        cases spanText? a <;> simp
      | artifact kk => simp [ContentOp.shown]
      | content s mc l => simp [ContentOp.shown]
    rw [hshown]
    refine ⟨⟨h3a, ?_, ?_, ?_⟩, h3o, by rw [h3s, h2s, h1s], ?_⟩
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
        simp only [hs, Bool.true_or, shownList_inSpan', String.append_empty]
      · rw [ite_eq_right hs]
        have hnone : actualOf (tagProps tg) = none := by
          cases h : actualOf (tagProps tg) with
          | none => rfl
          | some _ => simp [h] at hs
        simp only [hnone, Option.isSome_none, Bool.false_or, Option.getD_none, ite_self,
          String.append_empty]
  | .fill c x y w h, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl
  | .paint fl stk gs segs, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl
  | .image x y w h r, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl
  | .imageMissing x y w h, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl
  | .shade r g, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl
  | .outline fl stk segs, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl
  | .xobject m r kind body, st, k, i, ha =>
    reads_line res T _ (by intro _ h; cases h) (by intro _ _ h; cases h) (by intro _ _ _ _ h; cases h)
      (by simp [ContentOp.shown]) st ha rfl

theorem read_ops (res : Res) (T : Nat → Nat → String) (hT : FontReads res T) :
    ∀ (l : List ContentOp) (st : PdfTextRead.St) (k : Option Nat) (i : Bool), Agrees res st k i →
      Reads res ((opWordsGList l).map (·.tok)) st (ContentOp.shownList res T i k l).1 i
        (ContentOp.shownList res T i k l).2
  | [], st, k, i, ha => ⟨ha, rfl, rfl, by simp [ContentOp.shownList, opWordsGList]⟩
  | o :: rest, st, k, i, ha => by
    obtain ⟨a1, o1, s1, t1⟩ := read_op res T hT o st k i ha
    obtain ⟨a2, o2, s2, t2⟩ := read_ops res T hT rest _ _ i a1
    unfold Reads
    simp only [opWordsGList, ContentOp.shownList, List.map_append, List.foldl_append]
    exact ⟨a2, o2.trans o1, s2.trans s1, by rw [t2, t1, String.append_assoc]⟩

end

/-- The text a content stream the writer spells reads as from its bytes, its colours and tags holding
the writer's spellings: each text object's glyphs' text in the font in force, a saved state restoring
the font after it, a span's actual text for its content, a painted form's text left to the form. -/
public theorem streamText_exact (res : Res) (T : Nat → Nat → String) (hT : FontReads res T)
    (ops : Array ContentOp) (h : ContentOp.SpelledList ops.toList) :
    itemsText (readToks res .unmarked (PdfContentLex.scan (render ops).toUTF8)).1 =
      (ContentOp.shownList res T false none ops.toList).2 := by
  rw [scan_render_page ops h]
  unfold readToks
  dsimp only
  rw [← Array.foldl_toList, List.toList_toArray]
  have h0 : Agrees res (PdfTextRead.St.init .unmarked Mat.id) none false := ⟨rfl, rfl, by simp, rfl⟩
  obtain ⟨-, -, -, ht⟩ := read_ops res T hT ops.toList _ none false h0
  rw [ht]
  simp [PdfTextRead.St.init, itemsText]

end LeanTex.Core.PdfContent
