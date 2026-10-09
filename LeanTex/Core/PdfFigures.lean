module

public import LeanTex.Core.GfxPdf

/-!
# The figure resources a document's pages name

A figure's operators name what they paint with — an ExtGState, a shading
pattern, a shading, a form — by number. The writer emits every page's
figures with every such name 0, interns what the operators ask for, by
content and in first-occurrence order (`collectList`), and renames each
operator to its request's place in that table (`nameOps`); a figure
raster is named by its place in the document's raster table from the
start. Renaming changes no mark a reader meets (`nameOps_marks_id`); every
name the renamed operators spell is a place in the table
(`nameOps_names_covers`); and every occurrence of one name names one
resource (`nameOps_occ_agree`), so the object the writer spells from a
name's first occurrence answers every other.

Requests compare field by field (`ContentOp.same`, `FigRes`'s decidable
equality): the operators' own `==` reads colours by their screen value,
which would merge two resources whose PDF colours differ.
-/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Gfx


/-! ## Structural equality of operators -/

mutual

/-- Text operators equal field by field — the colour's PDF rider
included, which the colour's own `==` leaves out. -/
@[expose] public def TextOp.same : TextOp → TextOp → Bool
  | .scale a, .scale b => decide (a = b)
  | .move x y, .move x' y' => decide (x = x') && decide (y = y')
  | .font r s, .font r' s' => decide (r = r') && decide (s = s')
  | .color c, .color c' => decide (c = c')
  | .show is, .show is' => decide (is = is')
  | .marked t b, .marked t' b' => decide (t = t') && TextOp.sameList b.toList b'.toList
  | _, _ => false

@[expose] public def TextOp.sameList : List TextOp → List TextOp → Bool
  | [], [] => true
  | a :: as, b :: bs => TextOp.same a b && TextOp.sameList as bs
  | _, _ => false

end

mutual

/-- Page operators equal field by field: what two requests for one
resource must be to share it. -/
@[expose] public def ContentOp.same : ContentOp → ContentOp → Bool
  | .fill c x y w h, .fill c' x' y' w' h' =>
    decide (c = c') && decide (x = x') && decide (y = y') && decide (w = w') && decide (h = h')
  | .paint fl st gs segs, .paint fl' st' gs' segs' =>
    decide (fl = fl') && decide (st = st') && decide (gs = gs') && decide (segs = segs')
  | .text ops, .text ops' => TextOp.sameList ops.toList ops'.toList
  | .image x y w h r, .image x' y' w' h' r' =>
    decide (x = x') && decide (y = y') && decide (w = w') && decide (h = h') && decide (r = r')
  | .imageMissing x y w h, .imageMissing x' y' w' h' =>
    decide (x = x') && decide (y = y') && decide (w = w') && decide (h = h')
  | .marked t b, .marked t' b' => decide (t = t') && ContentOp.sameList b.toList b'.toList
  | .group m gs clips b, .group m' gs' clips' b' =>
    decide (m = m') && decide (gs = gs') && decide (clips = clips') &&
      ContentOp.sameList b.toList b'.toList
  | .shade r g, .shade r' g' => decide (r = r') && decide (g = g')
  | .outline f s p, .outline f' s' p' => decide (f = f') && decide (s = s') && decide (p = p')
  | .xobject m r k b, .xobject m' r' k' b' =>
    decide (m = m') && decide (r = r') && decide (k = k') && ContentOp.sameList b.toList b'.toList
  | _, _ => false

@[expose] public def ContentOp.sameList : List ContentOp → List ContentOp → Bool
  | [], [] => true
  | a :: as, b :: bs => ContentOp.same a b && ContentOp.sameList as bs
  | _, _ => false

end

mutual

private theorem TextOp.same_sound : ∀ a b : TextOp, TextOp.same a b = true → a = b
  | .scale a, b, h => by cases b <;> simp_all [TextOp.same]
  | .move x y, b, h => by cases b <;> simp_all [TextOp.same]
  | .font r s, b, h => by cases b <;> simp_all [TextOp.same]
  | .color c, b, h => by cases b <;> simp_all [TextOp.same]
  | .show is, b, h => by cases b <;> simp_all [TextOp.same]
  | .marked t body, b, h => by
    cases b
    case marked t' body' =>
      simp only [TextOp.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, Array.toList_inj.mp (TextOp.sameList_sound _ _ h.2)]
    all_goals simp [TextOp.same] at h

private theorem TextOp.sameList_sound : ∀ a b : List TextOp, TextOp.sameList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [TextOp.sameList, Bool.and_eq_true] at h
    rw [TextOp.same_sound x y h.1, TextOp.sameList_sound xs ys h.2]
  | [], _ :: _, h => by simp [TextOp.sameList] at h
  | _ :: _, [], h => by simp [TextOp.sameList] at h

end

mutual

private theorem ContentOp.same_sound : ∀ a b : ContentOp, ContentOp.same a b = true → a = b
  | .fill .., b, h => by cases b <;> simp_all [ContentOp.same]
  | .paint .., b, h => by cases b <;> simp_all [ContentOp.same]
  | .text ops, b, h => by
    cases b
    case text ops' =>
      simp only [ContentOp.same] at h
      rw [Array.toList_inj.mp (TextOp.sameList_sound _ _ h)]
    all_goals simp [ContentOp.same] at h
  | .image .., b, h => by cases b <;> simp_all [ContentOp.same]
  | .imageMissing .., b, h => by cases b <;> simp_all [ContentOp.same]
  | .marked t body, b, h => by
    cases b
    case marked t' body' =>
      simp only [ContentOp.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, Array.toList_inj.mp (ContentOp.sameList_sound _ _ h.2)]
    all_goals simp [ContentOp.same] at h
  | .group m gs clips body, b, h => by
    cases b
    case group m' gs' clips' body' =>
      simp only [ContentOp.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, Array.toList_inj.mp (ContentOp.sameList_sound _ _ h.2)]
    all_goals simp [ContentOp.same] at h
  | .shade .., b, h => by cases b <;> simp_all [ContentOp.same]
  | .outline .., b, h => by cases b <;> simp_all [ContentOp.same]
  | .xobject m r k body, b, h => by
    cases b
    case xobject m' r' k' body' =>
      simp only [ContentOp.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, Array.toList_inj.mp (ContentOp.sameList_sound _ _ h.2)]
    all_goals simp [ContentOp.same] at h

private theorem ContentOp.sameList_sound :
    ∀ a b : List ContentOp, ContentOp.sameList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [ContentOp.sameList, Bool.and_eq_true] at h
    rw [ContentOp.same_sound x y h.1, ContentOp.sameList_sound xs ys h.2]
  | [], _ :: _, h => by simp [ContentOp.sameList] at h
  | _ :: _, [], h => by simp [ContentOp.sameList] at h

end

mutual

private theorem TextOp.same_refl : ∀ a : TextOp, TextOp.same a a = true
  | .scale _ => by simp [TextOp.same]
  | .move _ _ => by simp [TextOp.same]
  | .font _ _ => by simp [TextOp.same]
  | .color _ => by simp [TextOp.same]
  | .show _ => by simp [TextOp.same]
  | .marked _ b => by simp [TextOp.same, TextOp.sameList_refl b.toList]

private theorem TextOp.sameList_refl : ∀ a : List TextOp, TextOp.sameList a a = true
  | [] => rfl
  | x :: xs => by simp [TextOp.sameList, TextOp.same_refl x, TextOp.sameList_refl xs]

end

mutual

private theorem ContentOp.same_refl : ∀ a : ContentOp, ContentOp.same a a = true
  | .fill .. => by simp [ContentOp.same]
  | .paint .. => by simp [ContentOp.same]
  | .text ops => by simp [ContentOp.same, TextOp.sameList_refl]
  | .image .. => by simp [ContentOp.same]
  | .imageMissing .. => by simp [ContentOp.same]
  | .marked _ b => by simp [ContentOp.same, ContentOp.sameList_refl b.toList]
  | .group _ _ _ b => by simp [ContentOp.same, ContentOp.sameList_refl b.toList]
  | .shade .. => by simp [ContentOp.same]
  | .outline .. => by simp [ContentOp.same]
  | .xobject _ _ _ b => by simp [ContentOp.same, ContentOp.sameList_refl b.toList]

private theorem ContentOp.sameList_refl : ∀ a : List ContentOp, ContentOp.sameList a a = true
  | [] => rfl
  | x :: xs => by simp [ContentOp.sameList, ContentOp.same_refl x, ContentOp.sameList_refl xs]

end

/-! ## Figure resources -/

/-- What a name in a content stream stands for, keyed by content: two
requests share a resource exactly when they are equal, field by field. -/
public inductive FigRes where
  | extG (fill stroke : Alpha)
  | pattern (g : Gradient)
  | shading (g : Gradient)
  | form (kind : FormKind) (body : Array ContentOp)
  deriving Repr, Inhabited

@[expose] public def FigRes.same : FigRes → FigRes → Bool
  | .extG a b, .extG a' b' => decide (a = a') && decide (b = b')
  | .pattern g, .pattern g' => decide (g = g')
  | .shading g, .shading g' => decide (g = g')
  | .form k b, .form k' b' => decide (k = k') && ContentOp.sameList b.toList b'.toList
  | _, _ => false

public theorem FigRes.same_sound : ∀ a b : FigRes, FigRes.same a b = true → a = b
  | .extG .., b, h => by cases b <;> simp_all [FigRes.same]
  | .pattern .., b, h => by cases b <;> simp_all [FigRes.same]
  | .shading .., b, h => by cases b <;> simp_all [FigRes.same]
  | .form k body, b, h => by
    cases b
    case form k' body' =>
      simp only [FigRes.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, Array.toList_inj.mp (ContentOp.sameList_sound _ _ h.2)]
    all_goals simp [FigRes.same] at h

public theorem FigRes.same_refl : ∀ a : FigRes, FigRes.same a a = true
  | .extG .. => by simp [FigRes.same]
  | .pattern .. => by simp [FigRes.same]
  | .shading .. => by simp [FigRes.same]
  | .form _ b => by simp [FigRes.same, ContentOp.sameList_refl b.toList]

public instance : DecidableEq FigRes := fun a b =>
  if h : FigRes.same a b = true then isTrue (FigRes.same_sound a b h)
  else isFalse fun e => h (e ▸ FigRes.same_refl a)

/-- `r` interned onto the table: kept where it already stands. -/
@[expose] public def intern (t : Array FigRes) (r : FigRes) : Array FigRes :=
  if t.contains r then t else t.push r

@[expose] public def paintReq (t : Array FigRes) : PdfPaint → Array FigRes
  | .solid _ => t
  | .pattern _ g => intern t (.pattern g)

@[expose] public def paintOptReq (t : Array FigRes) : Option PdfPaint → Array FigRes
  | some p => paintReq t p
  | none => t

@[expose] public def fillReq (t : Array FigRes) : Option PaintFill → Array FigRes
  | some f => paintReq t f.paint
  | none => t

@[expose] public def strokeReq (t : Array FigRes) : Option PaintStroke → Array FigRes
  | some s => paintReq t s.paint
  | none => t

@[expose] public def extGReq (t : Array FigRes) : Option ExtG → Array FigRes
  | some g => intern t (.extG g.fill g.stroke)
  | none => t

mutual

-- conserves: none — a request table, not a rewrite; what it guarantees is
-- `nameOps_names_covers`.
/-- The requests an operator makes onto `t`, its bodies' first. -/
@[expose] public def collectOne (t : Array FigRes) : ContentOp → Array FigRes
  | .fill _ _ _ _ _ => t
  | .paint fl st gs _ => extGReq (strokeReq (fillReq t fl) st) gs
  | .text _ => t
  | .image _ _ _ _ _ => t
  | .imageMissing _ _ _ _ => t
  | .marked _ body => collectList t body.toList
  | .group _ gs _ body => collectList (extGReq t gs) body.toList
  | .shade _ g => intern t (.shading g)
  | .outline _ _ _ => t
  | .xobject _ _ kind body =>
    match kind with
    | .raster _ => collectList t body.toList
    | .symbol => intern (collectList t body.toList) (.form .symbol body)
    | .group => intern (collectList t body.toList) (.form .group body)
    | .stamp fp sp gs =>
      intern (extGReq (strokeReq (paintOptReq (collectList t body.toList) fp) sp) gs)
        (.form (.stamp (GfxPdf.stampReach sp)) body)

@[expose] public def collectList (t : Array FigRes) : List ContentOp → Array FigRes
  | [] => t
  | o :: rest => collectList (collectOne t o) rest

end

/-- A request's place in the table; one past its end when absent. -/
@[expose] public def nameOf (t : Array FigRes) (r : FigRes) : Nat :=
  match t.finIdxOf? r with
  | some i => i.val
  | none => t.size

@[expose] public def namePaint (t : Array FigRes) : PdfPaint → PdfPaint
  | .solid c => .solid c
  | .pattern _ g => .pattern (nameOf t (.pattern g)) g

@[expose] public def nameFill (t : Array FigRes) (f : PaintFill) : PaintFill :=
  { f with paint := namePaint t f.paint }

@[expose] public def nameStroke (t : Array FigRes) (s : PaintStroke) : PaintStroke :=
  { s with paint := namePaint t s.paint }

@[expose] public def nameExtG (t : Array FigRes) (g : ExtG) : ExtG :=
  { g with res := nameOf t (.extG g.fill g.stroke) }

mutual

-- conserves: none — renaming keeps every mark (`nameOps_marks_id`).
/-- An operator with every name its request's place in `t`. A form is
looked up by the body the requests were collected from, then its body
renamed. -/
@[expose] public def nameOne (t : Array FigRes) : ContentOp → ContentOp
  | .fill c x y w h => .fill c x y w h
  | .paint fl st gs segs => .paint (fl.map (nameFill t)) (st.map (nameStroke t)) (gs.map (nameExtG t)) segs
  | .text ops => .text ops
  | .image x y w h res => .image x y w h res
  | .imageMissing x y w h => .imageMissing x y w h
  | .marked tag body => .marked tag (nameList t #[] body.toList)
  | .group m gs clips body => .group m (gs.map (nameExtG t)) clips (nameList t #[] body.toList)
  | .shade _ g => .shade (nameOf t (.shading g)) g
  | .outline fl st segs => .outline fl st segs
  | .xobject m res kind body =>
    match kind with
    | .raster k => .xobject m res (.raster k) (nameList t #[] body.toList)
    | .symbol => .xobject m (nameOf t (.form .symbol body)) .symbol (nameList t #[] body.toList)
    | .group => .xobject m (nameOf t (.form .group body)) .group (nameList t #[] body.toList)
    | .stamp fp sp gs =>
      .xobject m (nameOf t (.form (.stamp (GfxPdf.stampReach sp)) body))
        (.stamp (fp.map (namePaint t)) (sp.map (nameStroke t)) (gs.map (nameExtG t)))
        (nameList t #[] body.toList)

@[expose] public def nameList (t : Array FigRes) (acc : Array ContentOp) :
    List ContentOp → Array ContentOp
  | [] => acc
  | o :: rest => nameList t (acc.push (nameOne t o)) rest

end

/-- A page's operators renamed onto the table. -/
@[expose] public def nameOps (t : Array FigRes) (ops : Array ContentOp) : Array ContentOp :=
  nameList t #[] ops.toList

/-! ## Renaming moves no mark -/

private theorem nameList_acc (t : Array FigRes) (acc : Array ContentOp) (xs : List ContentOp) :
    nameList t acc xs = acc ++ nameList t #[] xs := by
  induction xs generalizing acc with
  | nil => simp [nameList]
  | cons o rest ih =>
    simp only [nameList]
    rw [ih, ih (#[].push _), Array.push_empty]
    simp

private theorem readList_append (rs : GfxPdf.RState) (acc : Array Mark) (a b : List ContentOp) :
    GfxPdf.readList rs acc (a ++ b) = GfxPdf.readList rs (GfxPdf.readList rs acc a) b := by
  induction a generalizing acc with
  | nil => rfl
  | cons o rest ih => exact ih _

private theorem readPaint_name (t : Array FigRes) (rs : GfxPdf.RState) (p : PdfPaint) :
    GfxPdf.readPaint rs (namePaint t p) = GfxPdf.readPaint rs p := by
  cases p <;> rfl

private theorem gs_fill_name (t : Array FigRes) (gs : Option ExtG) :
    (gs.map (nameExtG t)).map (·.fill) = gs.map (·.fill) := by
  cases gs <;> rfl

private theorem gs_stroke_name (t : Array FigRes) (gs : Option ExtG) :
    (gs.map (nameExtG t)).map (·.stroke) = gs.map (·.stroke) := by
  cases gs <;> rfl

private theorem readFill_name (t : Array FigRes) (rs : GfxPdf.RState) (gs : Option ExtG)
    (f : PaintFill) :
    GfxPdf.readFill rs (gs.map (nameExtG t)) (nameFill t f) = GfxPdf.readFill rs gs f := by
  obtain ⟨p, e⟩ := f
  cases p <;> cases gs <;> rfl

private theorem readStroke_name (t : Array FigRes) (rs : GfxPdf.RState) (gs : Option ExtG)
    (s : PaintStroke) :
    GfxPdf.readStroke rs (gs.map (nameExtG t)) (nameStroke t s) = GfxPdf.readStroke rs gs s := by
  obtain ⟨p, w, c, j, m, d⟩ := s
  cases p <;> cases gs <;> rfl

private theorem enterGroup_name (t : Array FigRes) (rs : GfxPdf.RState) (m : Option Affine)
    (gs : Option ExtG) (clips : Array (Array PathOp × Rule)) :
    rs.enterGroup m (gs.map (nameExtG t)) clips = rs.enterGroup m gs clips := by
  simp only [GfxPdf.RState.enterGroup, gs_fill_name, gs_stroke_name]

private theorem setPen_name (t : Array FigRes) (rs : GfxPdf.RState) (fp : Option PdfPaint)
    (sp : Option PaintStroke) (gs : Option ExtG) :
    rs.setPen (fp.map (namePaint t)) (sp.map (nameStroke t)) (gs.map (nameExtG t)) =
      rs.setPen fp sp gs := by
  cases fp <;> cases sp <;> cases gs <;>
    simp [GfxPdf.RState.setPen, readPaint_name, nameStroke, nameExtG]

mutual

private theorem readOne_name (t : Array FigRes) :
    ∀ (o : ContentOp) (rs : GfxPdf.RState) (acc : Array Mark),
      GfxPdf.readOne rs acc (nameOne t o) = GfxPdf.readOne rs acc o
  | .fill _ _ _ _ _, _, _ => rfl
  | .paint fl st gs segs, rs, acc => by
    have hf : (fl.map (nameFill t)).map (GfxPdf.readFill rs (gs.map (nameExtG t))) =
        fl.map (GfxPdf.readFill rs gs) := by
      cases fl with
      | none => rfl
      | some f => exact congrArg some (readFill_name t rs gs f)
    have hs : (st.map (nameStroke t)).map (GfxPdf.readStroke rs (gs.map (nameExtG t))) =
        st.map (GfxPdf.readStroke rs gs) := by
      cases st with
      | none => rfl
      | some s => exact congrArg some (readStroke_name t rs gs s)
    simp only [nameOne, GfxPdf.readOne]
    rw [hf, hs]
  | .text _, _, _ => rfl
  | .image _ _ _ _ _, _, _ => rfl
  | .imageMissing _ _ _ _, _, _ => rfl
  | .marked tag body, rs, acc => by
    simp only [nameOne, GfxPdf.readOne]
    exact readList_name t body.toList rs acc
  | .group m gs clips body, rs, acc => by
    simp only [nameOne, GfxPdf.readOne, enterGroup_name]
    exact readList_name t body.toList _ acc
  | .shade _ _, _, _ => rfl
  | .outline _ _ _, _, _ => rfl
  | .xobject m res kind body, rs, acc => by
    cases kind with
    | raster k => rfl
    | symbol =>
      simp only [nameOne, GfxPdf.readOne]
      exact readList_name t body.toList _ acc
    | group =>
      simp only [nameOne, GfxPdf.readOne]
      exact readList_name t body.toList _ acc
    | stamp fp sp gs =>
      simp only [nameOne, GfxPdf.readOne, setPen_name]
      exact readList_name t body.toList _ acc

private theorem readList_name (t : Array FigRes) :
    ∀ (xs : List ContentOp) (rs : GfxPdf.RState) (acc : Array Mark),
      GfxPdf.readList rs acc (nameList t #[] xs).toList = GfxPdf.readList rs acc xs
  | [], _, _ => rfl
  | o :: rest, rs, acc => by
    simp only [nameList]
    rw [nameList_acc, Array.toList_append, readList_append]
    simp only [Array.toList_push, List.nil_append, GfxPdf.readList]
    rw [readOne_name t o rs acc, readList_name t rest]

end

/-- **Renaming moves no mark** (`_id`): an operator's names choose which
resource object a viewer opens, never what the figure paints there — the
reading `GfxPdf.marks_projects` states is unchanged by the table's names. -/
public theorem nameOps_marks_id (t : Array FigRes) (place : Iso) (ops : Array ContentOp) :
    GfxPdf.readMarks place (nameOps t ops) = GfxPdf.readMarks place ops :=
  readList_name t ops.toList _ #[]

/-! ## No name dangles -/

@[expose] public def paintNames : PdfPaint → List Nat
  | .solid _ => []
  | .pattern res _ => [res]

@[expose] public def paintOptNames : Option PdfPaint → List Nat
  | some p => paintNames p
  | none => []

@[expose] public def fillNames : Option PaintFill → List Nat
  | some f => paintNames f.paint
  | none => []

@[expose] public def strokeNames : Option PaintStroke → List Nat
  | some s => paintNames s.paint
  | none => []

@[expose] public def extGNames : Option ExtG → List Nat
  | some g => [g.res]
  | none => []

mutual

-- conserves: none — a census of names, which `nameOps_names_covers` bounds.
/-- Every figure resource name an operator spells, its bodies' included. -/
@[expose] public def namesOne : ContentOp → List Nat
  | .fill _ _ _ _ _ => []
  | .paint fl st gs _ => fillNames fl ++ strokeNames st ++ (extGNames gs)
  | .text _ => []
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []
  | .marked _ body => namesList body.toList
  | .group _ gs _ body => extGNames gs ++ namesList body.toList
  | .shade res _ => [res]
  | .outline _ _ _ => []
  | .xobject _ res kind body =>
    match kind with
    | .raster _ => namesList body.toList
    | .symbol => res :: namesList body.toList
    | .group => res :: namesList body.toList
    | .stamp fp sp gs =>
      res :: (paintOptNames fp ++ strokeNames sp ++ extGNames gs ++ namesList body.toList)

@[expose] public def namesList : List ContentOp → List Nat
  | [] => []
  | o :: rest => namesOne o ++ (namesList rest)

end


private theorem intern_mem (t : Array FigRes) (r : FigRes) : r ∈ intern t r := by
  unfold intern
  split
  · next h => exact Array.contains_iff_mem.mp h
  · exact Array.mem_push_self

private theorem intern_sub {t : Array FigRes} {x : FigRes} (r : FigRes) (h : x ∈ t) :
    x ∈ intern t r := by
  unfold intern
  split
  · exact h
  · exact Array.mem_push_of_mem _ h

/-- A request in the table is named by its place there (`_exact`): the
entry at its name is the request. -/
public theorem nameOf_exact {t : Array FigRes} {r : FigRes} (h : r ∈ t) :
    ∃ hi : nameOf t r < t.size, t[nameOf t r] = r := by
  unfold nameOf
  cases hf : t.finIdxOf? r with
  | none => exact absurd h (Array.finIdxOf?_eq_none_iff.mp hf)
  | some i =>
    exact ⟨i.isLt, (Array.finIdxOf?_eq_some_iff.mp hf).1⟩


@[expose] public def paintReqs : PdfPaint → List FigRes
  | .solid _ => []
  | .pattern _ g => [.pattern g]

@[expose] public def paintOptReqs : Option PdfPaint → List FigRes
  | some p => paintReqs p
  | none => []

@[expose] public def fillReqs : Option PaintFill → List FigRes
  | some f => paintReqs f.paint
  | none => []

@[expose] public def strokeReqs : Option PaintStroke → List FigRes
  | some s => paintReqs s.paint
  | none => []

@[expose] public def extGReqs : Option ExtG → List FigRes
  | some g => [.extG g.fill g.stroke]
  | none => []

mutual

-- conserves: none — the requests an operator makes, which `collect` interns.
/-- Every request an operator makes, its bodies' first, as `collectOne` meets them. -/
@[expose] public def reqsOne : ContentOp → List FigRes
  | .fill _ _ _ _ _ => []
  | .paint fl st gs _ => fillReqs fl ++ strokeReqs st ++ (extGReqs gs)
  | .text _ => []
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []
  | .marked _ body => reqsList body.toList
  | .group _ gs _ body => extGReqs gs ++ reqsList body.toList
  | .shade _ g => [.shading g]
  | .outline _ _ _ => []
  | .xobject _ _ kind body =>
    match kind with
    | .raster _ => reqsList body.toList
    | .symbol => reqsList body.toList ++ [.form .symbol body]
    | .group => reqsList body.toList ++ [.form .group body]
    | .stamp fp sp gs =>
      reqsList body.toList ++ paintOptReqs fp ++ strokeReqs sp ++ extGReqs gs ++ [.form (.stamp (GfxPdf.stampReach sp)) body]

@[expose] public def reqsList : List ContentOp → List FigRes
  | [] => []
  | o :: rest => reqsOne o ++ (reqsList rest)

end

private theorem paintReq_sub {t : Array FigRes} {x : FigRes} (p : PdfPaint) (h : x ∈ t) :
    x ∈ paintReq t p := by
  cases p with
  | solid => exact h
  | pattern => exact intern_sub _ h

private theorem fillReq_sub {t : Array FigRes} {x : FigRes} (f : Option PaintFill) (h : x ∈ t) :
    x ∈ fillReq t f := by
  cases f with
  | none => exact h
  | some f => exact paintReq_sub _ h

private theorem strokeReq_sub {t : Array FigRes} {x : FigRes} (f : Option PaintStroke) (h : x ∈ t) :
    x ∈ strokeReq t f := by
  cases f with
  | none => exact h
  | some f => exact paintReq_sub _ h

private theorem extGReq_sub {t : Array FigRes} {x : FigRes} (g : Option ExtG) (h : x ∈ t) :
    x ∈ extGReq t g := by
  cases g with
  | none => exact h
  | some g => exact intern_sub _ h

private theorem paintOptReq_sub {t : Array FigRes} {x : FigRes} (p : Option PdfPaint) (h : x ∈ t) :
    x ∈ paintOptReq t p := by
  cases p with
  | none => exact h
  | some p => exact paintReq_sub _ h

private theorem paintReq_covers (t : Array FigRes) (p : PdfPaint) :
    ∀ r ∈ paintReqs p, r ∈ paintReq t p := by
  cases p with
  | solid => simp [paintReqs]
  | pattern _ g =>
    intro r hr
    simp only [paintReqs, List.mem_singleton] at hr
    subst hr
    exact intern_mem _ _

private theorem paintOptReq_covers (t : Array FigRes) (p : Option PdfPaint) :
    ∀ r ∈ paintOptReqs p, r ∈ paintOptReq t p := by
  cases p with
  | none => simp [paintOptReqs]
  | some p => exact paintReq_covers t p

private theorem fillReq_covers (t : Array FigRes) (f : Option PaintFill) :
    ∀ r ∈ fillReqs f, r ∈ fillReq t f := by
  cases f with
  | none => simp [fillReqs]
  | some f => exact paintReq_covers t f.paint

private theorem strokeReq_covers (t : Array FigRes) (f : Option PaintStroke) :
    ∀ r ∈ strokeReqs f, r ∈ strokeReq t f := by
  cases f with
  | none => simp [strokeReqs]
  | some f => exact paintReq_covers t f.paint

private theorem extGReq_covers (t : Array FigRes) (g : Option ExtG) :
    ∀ r ∈ extGReqs g, r ∈ extGReq t g := by
  cases g with
  | none => simp [extGReqs]
  | some g =>
    intro r hr
    simp only [extGReqs, List.mem_singleton] at hr
    subst hr
    exact intern_mem _ _

mutual

private theorem collectOne_sub {x : FigRes} :
    ∀ (o : ContentOp) (t : Array FigRes), x ∈ t → x ∈ collectOne t o
  | .fill .., _, h => h
  | .paint fl st gs _, _, h => extGReq_sub _ (strokeReq_sub _ (fillReq_sub _ h))
  | .text _, _, h => h
  | .image .., _, h => h
  | .imageMissing .., _, h => h
  | .marked _ body, t, h => collectList_sub body.toList t h
  | .group _ gs _ body, t, h => collectList_sub body.toList _ (extGReq_sub _ h)
  | .shade _ g, _, h => intern_sub _ h
  | .outline _ _ _, _, h => h
  | .xobject _ res kind body, t, h => by
    cases kind with
    | raster => exact collectList_sub body.toList t h
    | symbol => exact intern_sub _ (collectList_sub body.toList t h)
    | group => exact intern_sub _ (collectList_sub body.toList t h)
    | stamp fp sp gs =>
      exact intern_sub _
        (extGReq_sub _ (strokeReq_sub _ (paintOptReq_sub _ (collectList_sub body.toList t h))))

private theorem collectList_sub {x : FigRes} :
    ∀ (xs : List ContentOp) (t : Array FigRes), x ∈ t → x ∈ collectList t xs
  | [], _, h => h
  | o :: rest, t, h => collectList_sub rest _ (collectOne_sub o t h)

end

mutual

private theorem collectOne_covers :
    ∀ (o : ContentOp) (t : Array FigRes), ∀ r ∈ reqsOne o, r ∈ collectOne t o
  | .fill .., _, r, hr => by simp [reqsOne] at hr
  | .paint fl st gs _, t, r, hr => by
    simp only [reqsOne, List.mem_append] at hr
    simp only [collectOne]
    rcases hr with (hr | hr) | hr
    · exact extGReq_sub _ (strokeReq_sub _ (fillReq_covers t fl r hr))
    · exact extGReq_sub _ (strokeReq_covers _ st r hr)
    · exact extGReq_covers _ gs r hr
  | .text _, _, r, hr => by simp [reqsOne] at hr
  | .image .., _, r, hr => by simp [reqsOne] at hr
  | .imageMissing .., _, r, hr => by simp [reqsOne] at hr
  | .marked _ body, t, r, hr => collectList_covers body.toList t r hr
  | .group _ gs _ body, t, r, hr => by
    simp only [reqsOne, List.mem_append] at hr
    simp only [collectOne]
    rcases hr with hr | hr
    · exact collectList_sub body.toList _ (extGReq_covers t gs r hr)
    · exact collectList_covers body.toList _ r hr
  | .shade _ g, t, r, hr => by
    simp only [reqsOne, List.mem_singleton] at hr
    subst hr
    exact intern_mem _ _
  | .outline _ _ _, _, r, hr => by simp [reqsOne] at hr
  | .xobject _ res kind body, t, r, hr => by
    cases kind with
    | raster =>
      simp only [reqsOne] at hr
      simp only [collectOne]
      exact collectList_covers body.toList t r hr
    | symbol =>
      simp only [reqsOne, List.mem_append, List.mem_singleton] at hr
      simp only [collectOne]
      rcases hr with hr | hr
      · exact intern_sub _ (collectList_covers body.toList t r hr)
      · subst hr; exact intern_mem _ _
    | group =>
      simp only [reqsOne, List.mem_append, List.mem_singleton] at hr
      simp only [collectOne]
      rcases hr with hr | hr
      · exact intern_sub _ (collectList_covers body.toList t r hr)
      · subst hr; exact intern_mem _ _
    | stamp fp sp gs =>
      simp only [reqsOne, List.mem_append, List.mem_singleton] at hr
      simp only [collectOne]
      rcases hr with (((hr | hr) | hr) | hr) | hr
      · exact intern_sub _ (extGReq_sub _ (strokeReq_sub _
          (paintOptReq_sub _ (collectList_covers body.toList t r hr))))
      · exact intern_sub _ (extGReq_sub _ (strokeReq_sub _ (paintOptReq_covers _ fp r hr)))
      · exact intern_sub _ (extGReq_sub _ (strokeReq_covers _ sp r hr))
      · exact intern_sub _ (extGReq_covers _ gs r hr)
      · subst hr; exact intern_mem _ _

private theorem collectList_covers :
    ∀ (xs : List ContentOp) (t : Array FigRes), ∀ r ∈ reqsList xs, r ∈ collectList t xs
  | [], _, r, hr => by simp [reqsList] at hr
  | o :: rest, t, r, hr => by
    simp only [reqsList, List.mem_append] at hr
    simp only [collectList]
    rcases hr with hr | hr
    · exact collectList_sub rest _ (collectOne_covers o t r hr)
    · exact collectList_covers rest _ r hr

end

private theorem nameOf_lt {t : Array FigRes} {r : FigRes} (h : r ∈ t) : nameOf t r < t.size :=
  (nameOf_exact h).1

private theorem paintNames_lt (T : Array FigRes) (p : PdfPaint) (h : ∀ r ∈ paintReqs p, r ∈ T) :
    ∀ n ∈ paintNames (namePaint T p), n < T.size := by
  cases p with
  | solid => simp [namePaint, paintNames]
  | pattern _ g =>
    intro n hn
    simp only [namePaint, paintNames, List.mem_singleton] at hn
    subst hn
    exact nameOf_lt (h _ (by simp [paintReqs]))

private theorem paintOptNames_lt (T : Array FigRes) (p : Option PdfPaint)
    (h : ∀ r ∈ paintOptReqs p, r ∈ T) :
    ∀ n ∈ paintOptNames (p.map (namePaint T)), n < T.size := by
  cases p with
  | none => simp [paintOptNames]
  | some p => exact paintNames_lt T p h

private theorem fillNames_lt (T : Array FigRes) (f : Option PaintFill) (h : ∀ r ∈ fillReqs f, r ∈ T) :
    ∀ n ∈ fillNames (f.map (nameFill T)), n < T.size := by
  cases f with
  | none => simp [fillNames]
  | some f => exact paintNames_lt T f.paint h

private theorem strokeNames_lt (T : Array FigRes) (f : Option PaintStroke)
    (h : ∀ r ∈ strokeReqs f, r ∈ T) :
    ∀ n ∈ strokeNames (f.map (nameStroke T)), n < T.size := by
  cases f with
  | none => simp [strokeNames]
  | some f => exact paintNames_lt T f.paint h

private theorem extGNames_lt (T : Array FigRes) (g : Option ExtG) (h : ∀ r ∈ extGReqs g, r ∈ T) :
    ∀ n ∈ extGNames (g.map (nameExtG T)), n < T.size := by
  cases g with
  | none => simp [extGNames]
  | some g =>
    intro n hn
    simp only [Option.map_some, extGNames, nameExtG, List.mem_singleton] at hn
    subst hn
    exact nameOf_lt (h _ (by simp [extGReqs]))

private theorem namesList_append (a b : List ContentOp) :
    namesList (a ++ b) = namesList a ++ namesList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [namesList, ih]

mutual

private theorem namesOne_lt (T : Array FigRes) :
    ∀ o : ContentOp, (∀ r ∈ reqsOne o, r ∈ T) → ∀ n ∈ namesOne (nameOne T o), n < T.size
  | .fill .., _, n, hn => by simp [nameOne, namesOne] at hn
  | .paint fl st gs _, h, n, hn => by
    simp only [nameOne, namesOne, List.mem_append] at hn
    simp only [reqsOne, List.mem_append] at h
    rcases hn with (hn | hn) | hn
    · exact fillNames_lt T fl (fun r hr => h r (Or.inl (Or.inl hr))) n hn
    · exact strokeNames_lt T st (fun r hr => h r (Or.inl (Or.inr hr))) n hn
    · exact extGNames_lt T gs (fun r hr => h r (Or.inr hr)) n hn
  | .text _, _, n, hn => by simp [nameOne, namesOne] at hn
  | .image .., _, n, hn => by simp [nameOne, namesOne] at hn
  | .imageMissing .., _, n, hn => by simp [nameOne, namesOne] at hn
  | .marked _ body, h, n, hn => by
    simp only [nameOne, namesOne] at hn
    exact namesList_lt T body.toList h n hn
  | .group _ gs _ body, h, n, hn => by
    simp only [nameOne, namesOne, List.mem_append] at hn
    simp only [reqsOne, List.mem_append] at h
    rcases hn with hn | hn
    · exact extGNames_lt T gs (fun r hr => h r (Or.inl hr)) n hn
    · exact namesList_lt T body.toList (fun r hr => h r (Or.inr hr)) n hn
  | .shade _ g, h, n, hn => by
    simp only [nameOne, namesOne, List.mem_singleton] at hn
    subst hn
    exact nameOf_lt (h _ (by simp [reqsOne]))
  | .outline .., _, n, hn => by simp [nameOne, namesOne] at hn
  | .xobject _ res kind body, h, n, hn => by
    cases kind with
    | raster =>
      simp only [nameOne, namesOne] at hn
      simp only [reqsOne] at h
      exact namesList_lt T body.toList h n hn
    | symbol =>
      simp only [nameOne, namesOne, List.mem_cons] at hn
      simp only [reqsOne, List.mem_append, List.mem_singleton] at h
      rcases hn with hn | hn
      · subst hn; exact nameOf_lt (h _ (Or.inr rfl))
      · exact namesList_lt T body.toList (fun r hr => h r (Or.inl hr)) n hn
    | group =>
      simp only [nameOne, namesOne, List.mem_cons] at hn
      simp only [reqsOne, List.mem_append, List.mem_singleton] at h
      rcases hn with hn | hn
      · subst hn; exact nameOf_lt (h _ (Or.inr rfl))
      · exact namesList_lt T body.toList (fun r hr => h r (Or.inl hr)) n hn
    | stamp fp sp gs =>
      simp only [nameOne, namesOne, List.mem_cons, List.mem_append] at hn
      simp only [reqsOne, List.mem_append, List.mem_singleton] at h
      rcases hn with hn | (((hn | hn) | hn) | hn)
      · subst hn; exact nameOf_lt (h _ (Or.inr rfl))
      · exact paintOptNames_lt T fp (fun r hr => h r (by simp [hr])) n hn
      · exact strokeNames_lt T sp (fun r hr => h r (by simp [hr])) n hn
      · exact extGNames_lt T gs (fun r hr => h r (by simp [hr])) n hn
      · exact namesList_lt T body.toList (fun r hr => h r (by simp [hr])) n hn

private theorem namesList_lt (T : Array FigRes) :
    ∀ xs : List ContentOp, (∀ r ∈ reqsList xs, r ∈ T) →
      ∀ n ∈ namesList (nameList T #[] xs).toList, n < T.size
  | [], _, n, hn => by simp [nameList, namesList] at hn
  | o :: rest, h, n, hn => by
    simp only [nameList] at hn
    rw [nameList_acc, Array.toList_append, namesList_append] at hn
    simp only [Array.toList_push, List.nil_append, namesList, List.append_nil,
      List.mem_append] at hn
    simp only [reqsList, List.mem_append] at h
    rcases hn with hn | hn
    · exact namesOne_lt T o (fun r hr => h r (Or.inl hr)) n hn
    · exact namesList_lt T rest (fun r hr => h r (Or.inr hr)) n hn

end

/-- **No name dangles** (`_covers`): every resource name the renamed
operators spell is a place in the table collected from those same
operators, so the resources dictionary the writer builds from the table
answers every name a page or form asks for. -/
public theorem nameOps_names_covers (ops : Array ContentOp) :
    ∀ n ∈ namesList (nameOps (collectList #[] ops.toList) ops).toList,
      n < (collectList #[] ops.toList).size :=
  namesList_lt _ ops.toList (collectList_covers ops.toList #[])


/-! ## One name, one resource -/

/-- A table entry as the writer spells it: a form's body renamed onto the
same table. -/
@[expose] public def nameRes (t : Array FigRes) : FigRes → FigRes
  | .extG a b => .extG a b
  | .pattern g => .pattern g
  | .shading g => .shading g
  | .form kind body => .form kind (nameList t #[] body.toList)

@[expose] public def paintOcc : PdfPaint → List (Nat × FigRes)
  | .solid _ => []
  | .pattern res g => [(res, .pattern g)]

@[expose] public def paintOptOcc : Option PdfPaint → List (Nat × FigRes)
  | some p => paintOcc p
  | none => []

@[expose] public def fillOcc : Option PaintFill → List (Nat × FigRes)
  | some f => paintOcc f.paint
  | none => []

@[expose] public def strokeOcc : Option PaintStroke → List (Nat × FigRes)
  | some s => paintOcc s.paint
  | none => []

@[expose] public def extGOcc : Option ExtG → List (Nat × FigRes)
  | some g => [(g.res, .extG g.fill g.stroke)]
  | none => []

mutual

-- conserves: none — the names an operator spells with what each names,
-- which `nameOps_occ_agree` holds to one resource per name.
/-- Every resource an operator names, with its name, its bodies' first —
what the writer spells one object per name from. -/
@[expose] public def occOne : ContentOp → List (Nat × FigRes)
  | .fill _ _ _ _ _ => []
  | .paint fl st gs _ => fillOcc fl ++ strokeOcc st ++ (extGOcc gs)
  | .text _ => []
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []
  | .marked _ body => occList body.toList
  | .group _ gs _ body => extGOcc gs ++ occList body.toList
  | .shade res g => [(res, .shading g)]
  | .outline _ _ _ => []
  | .xobject _ res kind body =>
    match kind with
    | .raster _ => occList body.toList
    | .symbol => occList body.toList ++ [(res, .form .symbol body)]
    | .group => occList body.toList ++ [(res, .form .group body)]
    | .stamp fp sp gs =>
      occList body.toList ++ paintOptOcc fp ++ strokeOcc sp ++ extGOcc gs ++
        [(res, .form (.stamp (GfxPdf.stampReach sp)) body)]

@[expose] public def occList : List ContentOp → List (Nat × FigRes)
  | [] => []
  | o :: rest => occOne o ++ (occList rest)

end

private theorem occList_append (a b : List ContentOp) : occList (a ++ b) = occList a ++ occList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [occList, ih]

private theorem paintOcc_name (T : Array FigRes) (p : PdfPaint) :
    ∀ q ∈ paintOcc (namePaint T p), ∃ r ∈ paintReqs p, q = (nameOf T r, nameRes T r) := by
  cases p with
  | solid => simp [namePaint, paintOcc]
  | pattern _ g =>
    intro q hq
    simp only [namePaint, paintOcc, List.mem_singleton] at hq
    exact ⟨.pattern g, by simp [paintReqs], by rw [hq]; rfl⟩

private theorem paintOptOcc_name (T : Array FigRes) (p : Option PdfPaint) :
    ∀ q ∈ paintOptOcc (p.map (namePaint T)), ∃ r ∈ paintOptReqs p, q = (nameOf T r, nameRes T r) := by
  cases p with
  | none => simp [paintOptOcc]
  | some p => exact paintOcc_name T p

private theorem fillOcc_name (T : Array FigRes) (f : Option PaintFill) :
    ∀ q ∈ fillOcc (f.map (nameFill T)), ∃ r ∈ fillReqs f, q = (nameOf T r, nameRes T r) := by
  cases f with
  | none => simp [fillOcc]
  | some f => exact paintOcc_name T f.paint

private theorem strokeOcc_name (T : Array FigRes) (f : Option PaintStroke) :
    ∀ q ∈ strokeOcc (f.map (nameStroke T)), ∃ r ∈ strokeReqs f, q = (nameOf T r, nameRes T r) := by
  cases f with
  | none => simp [strokeOcc]
  | some f => exact paintOcc_name T f.paint

private theorem extGOcc_name (T : Array FigRes) (g : Option ExtG) :
    ∀ q ∈ extGOcc (g.map (nameExtG T)), ∃ r ∈ extGReqs g, q = (nameOf T r, nameRes T r) := by
  cases g with
  | none => simp [extGOcc]
  | some g =>
    intro q hq
    simp only [Option.map_some, extGOcc, nameExtG, List.mem_singleton] at hq
    exact ⟨.extG g.fill g.stroke, by simp [extGReqs], by rw [hq]; rfl⟩

/-- Renaming a stroke's paint moves no reach. -/
private theorem stampReach_name (T : Array FigRes) (sp : Option PaintStroke) :
    GfxPdf.stampReach (sp.map (nameStroke T)) = GfxPdf.stampReach sp := by
  cases sp <;> rfl

mutual

private theorem occOne_name (T : Array FigRes) :
    ∀ o : ContentOp, ∀ q ∈ occOne (nameOne T o), ∃ r ∈ reqsOne o, q = (nameOf T r, nameRes T r)
  | .fill .., q, hq => by simp [nameOne, occOne] at hq
  | .paint fl st gs _, q, hq => by
    simp only [nameOne, occOne, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨r, hr, e⟩ := fillOcc_name T fl q hq
      exact ⟨r, by simp [reqsOne, hr], e⟩
    · obtain ⟨r, hr, e⟩ := strokeOcc_name T st q hq
      exact ⟨r, by simp [reqsOne, hr], e⟩
    · obtain ⟨r, hr, e⟩ := extGOcc_name T gs q hq
      exact ⟨r, by simp [reqsOne, hr], e⟩
  | .text _, q, hq => by simp [nameOne, occOne] at hq
  | .image .., q, hq => by simp [nameOne, occOne] at hq
  | .imageMissing .., q, hq => by simp [nameOne, occOne] at hq
  | .marked _ body, q, hq => by
    simp only [nameOne, occOne] at hq
    exact occList_name T body.toList q hq
  | .group _ gs _ body, q, hq => by
    simp only [nameOne, occOne, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨r, hr, e⟩ := extGOcc_name T gs q hq
      exact ⟨r, by simp [reqsOne, hr], e⟩
    · obtain ⟨r, hr, e⟩ := occList_name T body.toList q hq
      exact ⟨r, by simp [reqsOne, hr], e⟩
  | .shade _ g, q, hq => by
    simp only [nameOne, occOne, List.mem_singleton] at hq
    exact ⟨.shading g, by simp [reqsOne], by rw [hq]; rfl⟩
  | .outline .., q, hq => by simp [nameOne, occOne] at hq
  | .xobject _ _ kind body, q, hq => by
    cases kind with
    | raster =>
      simp only [nameOne, occOne] at hq
      obtain ⟨r, hr, e⟩ := occList_name T body.toList q hq
      exact ⟨r, by simp [reqsOne, hr], e⟩
    | symbol =>
      simp only [nameOne, occOne, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | hq
      · obtain ⟨r, hr, e⟩ := occList_name T body.toList q hq
        exact ⟨r, by simp [reqsOne, hr], e⟩
      · exact ⟨.form .symbol body, by simp [reqsOne], by rw [hq]; rfl⟩
    | group =>
      simp only [nameOne, occOne, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | hq
      · obtain ⟨r, hr, e⟩ := occList_name T body.toList q hq
        exact ⟨r, by simp [reqsOne, hr], e⟩
      · exact ⟨.form .group body, by simp [reqsOne], by rw [hq]; rfl⟩
    | stamp fp sp gs =>
      simp only [nameOne, occOne, List.mem_append, List.mem_singleton] at hq
      rcases hq with (((hq | hq) | hq) | hq) | hq
      · obtain ⟨r, hr, e⟩ := occList_name T body.toList q hq
        exact ⟨r, by simp [reqsOne, hr], e⟩
      · obtain ⟨r, hr, e⟩ := paintOptOcc_name T fp q hq
        exact ⟨r, by simp [reqsOne, hr], e⟩
      · obtain ⟨r, hr, e⟩ := strokeOcc_name T sp q hq
        exact ⟨r, by simp [reqsOne, hr], e⟩
      · obtain ⟨r, hr, e⟩ := extGOcc_name T gs q hq
        exact ⟨r, by simp [reqsOne, hr], e⟩
      · exact ⟨.form (.stamp (GfxPdf.stampReach sp)) body, by simp [reqsOne],
          by rw [hq, stampReach_name]; rfl⟩

private theorem occList_name (T : Array FigRes) :
    ∀ xs : List ContentOp, ∀ q ∈ occList (nameList T #[] xs).toList,
      ∃ r ∈ reqsList xs, q = (nameOf T r, nameRes T r)
  | [], q, hq => by simp [nameList, occList] at hq
  | o :: rest, q, hq => by
    simp only [nameList] at hq
    rw [nameList_acc, Array.toList_append, occList_append] at hq
    simp only [Array.toList_push, List.nil_append, occList, List.append_nil, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨r, hr, e⟩ := occOne_name T o q hq
      exact ⟨r, by simp [reqsList, hr], e⟩
    · obtain ⟨r, hr, e⟩ := occList_name T rest q hq
      exact ⟨r, by simp [reqsList, hr], e⟩

end

/-- **One name, one resource** (`_agree`): every occurrence of a name in the
renamed operators names the same resource, so the object the writer spells
from a name's first occurrence is what every other occurrence asks for — a
name is a request's place in the table, and the table holds each request
once. -/
public theorem nameOps_occ_agree (ops : Array ContentOp) :
    ∀ p ∈ occList (nameOps (collectList #[] ops.toList) ops).toList,
    ∀ q ∈ occList (nameOps (collectList #[] ops.toList) ops).toList,
      p.1 = q.1 → p.2 = q.2 := by
  intro p hp q hq he
  obtain ⟨r, hr, rfl⟩ := occList_name _ ops.toList p hp
  obtain ⟨r', hr', rfl⟩ := occList_name _ ops.toList q hq
  have h1 := nameOf_exact (collectList_covers ops.toList #[] r hr)
  have h2 := nameOf_exact (collectList_covers ops.toList #[] r' hr')
  simp only at he ⊢
  obtain ⟨_, e1⟩ := h1
  obtain ⟨_, e2⟩ := h2
  have : r = r' := by
    rw [← e1, ← e2]
    simp only [he]
  rw [this]


mutual

-- conserves: none — `occList` accumulated, the walk the writer runs
-- (`occInto_exact`).
/-- `occOne` onto an accumulator. -/
@[expose] public def occOneInto (acc : Array (Nat × FigRes)) : ContentOp → Array (Nat × FigRes)
  | .fill _ _ _ _ _ => acc
  | .paint fl st gs _ => acc ++ (fillOcc fl ++ strokeOcc st ++ (extGOcc gs)).toArray
  | .text _ => acc
  | .image _ _ _ _ _ => acc
  | .imageMissing _ _ _ _ => acc
  | .marked _ body => occInto acc body.toList
  | .group _ gs _ body => occInto (acc ++ (extGOcc gs).toArray) body.toList
  | .shade res g => acc.push (res, .shading g)
  | .outline _ _ _ => acc
  | .xobject _ res kind body =>
    match kind with
    | .raster _ => occInto acc body.toList
    | .symbol => (occInto acc body.toList).push (res, .form .symbol body)
    | .group => (occInto acc body.toList).push (res, .form .group body)
    | .stamp fp sp gs =>
      ((occInto acc body.toList) ++ (paintOptOcc fp ++ strokeOcc sp ++ (extGOcc gs)).toArray).push
        (res, .form (.stamp (GfxPdf.stampReach sp)) body)

@[expose] public def occInto (acc : Array (Nat × FigRes)) : List ContentOp → Array (Nat × FigRes)
  | [] => acc
  | o :: rest => occInto (occOneInto acc o) rest

end

mutual

private theorem occOneInto_exact :
    ∀ (o : ContentOp) (acc : Array (Nat × FigRes)), occOneInto acc o = acc ++ (occOne o).toArray
  | .fill .., _ => by simp [occOneInto, occOne]
  | .paint .., _ => by simp [occOneInto, occOne]
  | .text _, _ => by simp [occOneInto, occOne]
  | .image .., _ => by simp [occOneInto, occOne]
  | .imageMissing .., _ => by simp [occOneInto, occOne]
  | .marked _ body, acc => by
    simp only [occOneInto, occOne]
    exact occInto_exact body.toList acc
  | .group _ gs _ body, acc => by
    simp only [occOneInto, occOne]
    rw [occInto_exact body.toList]
    simp
  | .shade .., _ => by simp [occOneInto, occOne]
  | .outline .., _ => by simp [occOneInto, occOne]
  | .xobject _ res kind body, acc => by
    cases kind with
    | raster =>
      simp only [occOneInto, occOne]
      exact occInto_exact body.toList acc
    | symbol =>
      simp only [occOneInto, occOne]
      rw [occInto_exact body.toList]
      simp
    | group =>
      simp only [occOneInto, occOne]
      rw [occInto_exact body.toList]
      simp
    | stamp fp sp gs =>
      simp only [occOneInto, occOne]
      rw [occInto_exact body.toList]
      simp

private theorem occInto_exact :
    ∀ (xs : List ContentOp) (acc : Array (Nat × FigRes)), occInto acc xs = acc ++ (occList xs).toArray
  | [], _ => by simp [occInto, occList]
  | o :: rest, acc => by
    simp only [occInto, occList]
    rw [occInto_exact rest, occOneInto_exact o]
    simp

end

/-- The writer's walk is the occurrence list (`_exact`): accumulated onto
an array, in the same order. -/
public theorem occInto_occList_exact (xs : List ContentOp) : occInto #[] xs = (occList xs).toArray := by
  simpa using occInto_exact xs #[]

end LeanTex.Core.Pdf
