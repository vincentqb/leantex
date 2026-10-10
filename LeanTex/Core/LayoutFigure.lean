module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Font
public import LeanTex.Core.Diag
public import LeanTex.Core.Image
public import LeanTex.Core.Layout
import LeanTex.Core.FigureLoss

/-!
# Text in an imported figure, set by the engine

An SVG's text runs (`Gfx.Run`) set in the document's own faces, with the
body text's arithmetic: each scalar's glyph from its face's cmap, its
advance from `hmtx` at the run's size, the face's pair kerns as body text
applies them (`pairKern`, under the one `Ir.features` record), and a scalar
the face lacks from the per-scalar fallback chain the font environment
precomputed (`FontSet.fallbackFor`, W0009 as in text). Once every run of a
text chunk is shaped, the chunk's anchor resolves from its advance (SVG 2
§11.10.2): `middle` centres the chunk on its start, `end` ends it there.

Which face a run asks for is the SVG's font list, read against the
document's roles, never against the host: a generic family is a role —
`serif` the body, `sans-serif` the sans (the body where the document names
none, as the font assembly resolves it), `monospace` the mono, and the
display generics the sans — and a named family is the role whose face has
that family name. The first family in the list that has a role decides;
a list that names none sets in the sans, and each family it named is
reported once. A weight of 600 or more takes the role's bold, an italic or
oblique style its italic. A host face is never loaded (`fontMatch_mem`).
-/

namespace LeanTex.Core.Layout

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Gfx

/-- The role a generic family names: 0 the body, 1 the sans, 2 the mono. -/
@[expose] public def roleOfGeneric (g : String) : Option Nat :=
  match g with
  | "serif" | "ui-serif" | "math" | "fangsong" => some 0
  | "sans-serif" | "ui-sans-serif" | "cursive" | "fantasy" | "system-ui" | "ui-rounded" | "emoji" =>
    some 1
  | "monospace" | "ui-monospace" => some 2
  | _ => none

/-- A family's role: a generic's, else the role whose regular face carries
that family name. -/
public def roleOf (fs : FontSet) (family : String) : Option Nat :=
  (roleOfGeneric family).orElse fun _ =>
    [0, 1, 2].find? fun r => (fs.get (fs.lookup r 400 false)).family.toLower == family.toLower

/-- The series a weight resolves to among the faces a role loads. -/
@[expose] public def seriesOf (weight : Nat) : Nat := if weight ≥ 600 then 700 else 400

/-- The role a run's family list resolves to: the first family with one,
else the sans — the role `fontMatch` looks its face up in. -/
@[expose] public def roleFor (fs : FontSet) (req : FaceReq) : Nat :=
  (req.families.findSome? (roleOf fs)).getD 1

/-- **A run's face**: the first family with a role, else the sans; and, when
the list named no role, its families, for the report. -/
public def fontMatch (fs : FontSet) (req : FaceReq) : Nat × Option (Array String) :=
  match req.families.findSome? (roleOf fs) with
  | some r => (fs.lookup r (seriesOf req.weight) req.italic, none)
  -- premise: svgFontMatchChecks — two builds differing only by the family a
  -- figure names: an unanswered family sets the face a generic sets, and only
  -- it is reported
  | none => (fs.lookup 1 (seriesOf req.weight) req.italic, some req.families)

/-- **A figure's text sets in one of the document's own role faces**
(`_mem`): whatever the SVG names, the face is the body's, the sans's or the
mono's at the requested series and style — never a face from outside the
document's font environment. -/
public theorem fontMatch_mem (fs : FontSet) (req : FaceReq) :
    (fontMatch fs req).1 ∈ [fs.lookup 0 (seriesOf req.weight) req.italic,
      fs.lookup 1 (seriesOf req.weight) req.italic, fs.lookup 2 (seriesOf req.weight) req.italic] := by
  unfold fontMatch
  split
  · next r h =>
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by
      obtain ⟨fam, -, hfam⟩ := Array.exists_of_findSome?_eq_some h
      unfold roleOf at hfam
      cases hg : roleOfGeneric fam with
      | some g =>
        rw [hg] at hfam
        simp only [Option.orElse_some, Option.some.injEq] at hfam
        subst hfam
        unfold roleOfGeneric at hg
        split at hg <;> simp_all
      | none =>
        rw [hg] at hfam
        simp only [Option.orElse_none] at hfam
        have := List.mem_of_find?_eq_some hfam
        simpa using this
    rcases hr with rfl | rfl | rfl <;> simp
  · simp

/-- A glyph's advance at `size`: its `hmtx` units scaled, as body text
scales them. -/
@[expose] public def advanceAt (size : Sp) (font : Font) (g : Nat) : Sp :=
  ((font.widths[g]?.getD 0) * size.toNat) / font.unitsPerEm

/-- What shaping one run gave: its glyphs — face, glyph, pen x from the
run's start — its advance, the substitutions the fallback chain made and
the scalars no face covers. -/
public structure RunShape where
  glyphs : Array (Nat × Nat × Char × Sp)
  advance : Sp
  substs : Array (Nat × Char × Nat)
  missing : Array Char
  deriving Inhabited

/-- **One run shaped** in face `face` at `size`. -/
public def shapeRun (fs : FontSet) (face : Nat) (size : Sp) (text : String) : RunShape := Id.run do
  let font := fs.get face
  let mut out : Array (Nat × Nat × Char × Sp) := #[]
  let mut x : Sp := 0
  let mut prev : Option (Nat × Nat) := none
  let mut substs : Array (Nat × Char × Nat) := #[]
  let mut missing : Array Char := #[]
  for c in text.toList do
    match font.gid c with
    | some g =>
      let k : Sp := match prev with
        | some (pf, pg) => if pf == face then pairKern Ir.features size font pg g else 0
        | none => 0
      x := x + k
      out := out.push (face, g, c, x)
      x := x + advanceAt size font g
      prev := some (face, g)
    | none =>
      match (fs.fallbackFor c).bind fun fb => ((fs.get fb).gid c).map (fb, ·) with
      | some (fb, g) =>
        out := out.push (fb, g, c, x)
        x := x + advanceAt size (fs.get fb) g
        prev := some (fb, g)
        unless substs.any (fun (f, d, _) => f == face && d == c) do substs := substs.push (face, c, fb)
      | none =>
        unless missing.contains c do missing := missing.push c
  return { glyphs := out, advance := x, substs, missing }

/-- What shaping a figure reports: the families no role answered, the
substitutions, the scalars no face covers. -/
public structure ShapeNotes where
  families : Array String
  substs : Array (Nat × Char × Nat)
  missing : Array Char
  deriving Inhabited

/-- A run as shaped, at its resolved start: the run's frame map with its
translation along x the chunk's pen at the run, shifted by the chunk's
anchor; its role, and the descriptors of the face its family list resolved
to (`fontMatch`). -/
@[expose] public def placeRun (fs : FontSet) (r : Run) (start : Sp) (sh : RunShape) : Shaped :=
  let face := fs.get (fontMatch fs r.face).1
  { size := r.size, xf := { r.xf with e := ((start : Int) : Rat) }, glyphs := sh.glyphs, text := r.text
    fill := r.fill, stroke := r.stroke, lang := r.lang, role := roleFor fs r.face
    weight := face.weight, italic := face.isItalic }

/-- The starts of a list's runs, chunk by chunk: a run that does not
follow starts a chunk at its own x, a following run continues the pen by
its offset, and once a chunk ends — at the next chunk, at any other node,
at the list's end — every run in it moves by the chunk's anchor shift. -/
public def chunkStarts (shapes : Array (Option (Run × RunShape))) : Array Sp := Id.run do
  let mut starts : Array Sp := Array.replicate shapes.size 0
  let mut chunk : Array Nat := #[]
  let mut x0 : Sp := 0
  let mut pen : Sp := 0
  let mut anchor : Anchor := .start
  let close (starts : Array Sp) (chunk : Array Nat) (x0 pen : Sp) (anchor : Anchor) : Array Sp :=
    let w := pen - x0
    let shift : Sp := match anchor with
      | .start => 0
      | .middle => -(w / 2)
      | .end => -w
    chunk.foldl (fun s k => s.modify k (· + shift)) starts
  for h : k in [0:shapes.size] do
    match shapes[k] with
    | some (r, sh) =>
      let off : Sp := (r.xf.e + 1 / 2).floor
      if !r.follows || chunk.isEmpty then
        starts := close starts chunk x0 pen anchor
        chunk := #[]
        x0 := if r.follows then pen + off else off
        pen := x0
        anchor := r.anchor
      else pen := pen + off
      starts := starts.set! k pen
      chunk := chunk.push k
      pen := pen + sh.advance
    | none =>
      starts := close starts chunk x0 pen anchor
      chunk := #[]
  return close starts chunk x0 pen anchor

/-- A list's runs shaped, each at its own face, in list order; a node
that is no run stands as `none`. -/
public def shapesOf (fs : FontSet) (ns : List (Node Run)) : Array (Option (Run × RunShape)) :=
  ns.toArray.map fun n => match n with
    | .label r => some (r, shapeRun fs (fontMatch fs r.face).1 r.size r.text)
    | .draw _ _ _ | .group _ _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .words _ => none

mutual

-- conserves: none — a shaping: each run maps to one shaped run carrying its
-- text, every other node to itself; `shapeFigure_text` states the census.
/-- One node shaped onto `acc`, a run at the start `pos` gives it; a
group's list shaped as `shapeList` shapes one. -/
public def shapeOne (fs : FontSet) (pos : Option (Sp × RunShape)) (acc : Array (Node Shaped)) :
    Node Run → Array (Node Shaped)
  | .draw g f s => acc.push (.draw g f s)
  | .group xf clips a kids =>
    let shapes := shapesOf fs kids.toList
    acc.push (.group xf clips a (shapeFrom fs shapes (chunkStarts shapes) 0 #[] kids.toList))
  | .use k xf => acc.push (.use k xf)
  | .stamp o xf f s => acc.push (.stamp o xf f s)
  | .image k xf => acc.push (.image k xf)
  | .label r =>
    match pos with
    | some (start, sh) => acc.push (.label (placeRun fs r start sh))
    | none => acc.push (.label (placeRun fs r 0 (shapeRun fs (fontMatch fs r.face).1 r.size r.text)))
  | .words w => acc.push (.words w)

/-- Each node of a list from index `i`, its run at the start its chunk
resolved. -/
public def shapeFrom (fs : FontSet) (shapes : Array (Option (Run × RunShape))) (starts : Array Sp)
    (i : Nat) (acc : Array (Node Shaped)) : List (Node Run) → Array (Node Shaped)
  | [] => acc
  | n :: rest =>
    let pos := (shapes[i]?.join).map fun (_, sh) => ((starts[i]?.getD 0), sh)
    shapeFrom fs shapes starts (i + 1) (shapeOne fs pos acc n) rest

end

/-- A list shaped: its runs shaped first, their chunks' starts resolved,
then each node in order. -/
public def shapeList (fs : FontSet) (ns : List (Node Run)) : Array (Node Shaped) :=
  let shapes := shapesOf fs ns
  shapeFrom fs shapes (chunkStarts shapes) 0 #[] ns

mutual

-- conserves: none — a census of a figure's runs.
/-- Every run of a tree onto `acc`. -/
public def runsOne (acc : Array Run) : Node Run → Array Run
  | .group _ _ _ kids => runsList acc kids.toList
  | .label r => acc.push r
  | .draw _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .words _ => acc

public def runsList (acc : Array Run) : List (Node Run) → Array Run
  | [] => acc
  | n :: rest => runsList (runsOne acc n) rest

end

/-- **A figure's text set** in the document's faces: every node and symbol
body shaped, and what the shaping reports. -/
public def shapeFigure (fs : FontSet) (fig : Figure Run) : Figure Shaped × ShapeNotes :=
  let nodes := shapeList fs fig.nodes.toList
  let symbols := fig.symbols.map fun s => shapeList fs s.toList
  let runs := fig.symbols.foldl (fun acc s => runsList acc s.toList) (runsList #[] fig.nodes.toList)
  let notes := runs.foldl (fun (n : ShapeNotes) r =>
    let (face, unmatched) := fontMatch fs r.face
    let sh := shapeRun fs face r.size r.text
    let fams := (unmatched.getD #[]).foldl (fun a f => if a.contains f then a else a.push f) n.families
    { families := fams
      substs := sh.substs.foldl (fun a s => if a.contains s then a else a.push s) n.substs
      missing := sh.missing.foldl (fun a c => if a.contains c then a else a.push c) n.missing })
    { families := #[], substs := #[], missing := #[] }
  ({ box := fig.box, clipToBox := fig.clipToBox, nodes, outlines := fig.outlines, symbols
     rasters := fig.rasters, title := fig.title, losses := fig.losses }, notes)

mutual

-- conserves: none — a census of a shaped tree's run texts, which
-- `shapeFigure_text` reads.
/-- Every shaped run's text in a tree, onto `acc`, in order. -/
public def shapedTextsOne (acc : Array String) : Node Shaped → Array String
  | .label s => acc.push s.text
  | .group _ _ _ kids => shapedTextsList acc kids.toList
  | .draw _ _ _ | .use _ _ | .stamp _ _ _ _ | .image _ _ | .words _ => acc
public def shapedTextsList (acc : Array String) : List (Node Shaped) → Array String
  | [] => acc
  | n :: rest => shapedTextsList (shapedTextsOne acc n) rest
end

mutual
private theorem shapedTextsOne_acc (acc : Array String) (n : Node Shaped) :
    shapedTextsOne acc n = acc ++ shapedTextsOne #[] n := by
  cases n with
  | label s => simp [shapedTextsOne]
  | group xf c a kids => simp only [shapedTextsOne]; exact shapedTextsList_acc acc kids.toList
  | draw _ _ _ => simp [shapedTextsOne]
  | use _ _ => simp [shapedTextsOne]
  | stamp _ _ _ _ => simp [shapedTextsOne]
  | image _ _ => simp [shapedTextsOne]
  | words _ => simp [shapedTextsOne]
private theorem shapedTextsList_acc (acc : Array String) (xs : List (Node Shaped)) :
    shapedTextsList acc xs = acc ++ shapedTextsList #[] xs := by
  match xs with
  | [] => simp [shapedTextsList]
  | n :: rest =>
    simp only [shapedTextsList]
    rw [shapedTextsList_acc _ rest, shapedTextsList_acc (shapedTextsOne #[] n) rest,
      shapedTextsOne_acc acc n, Array.append_assoc]
end

mutual
private theorem runsOne_acc (acc : Array Run) (n : Node Run) : runsOne acc n = acc ++ runsOne #[] n := by
  cases n with
  | label r => simp [runsOne]
  | group xf c a kids => simp only [runsOne]; exact runsList_acc acc kids.toList
  | draw _ _ _ => simp [runsOne]
  | use _ _ => simp [runsOne]
  | stamp _ _ _ _ => simp [runsOne]
  | image _ _ => simp [runsOne]
  | words _ => simp [runsOne]
private theorem runsList_acc (acc : Array Run) (xs : List (Node Run)) :
    runsList acc xs = acc ++ runsList #[] xs := by
  match xs with
  | [] => simp [runsList]
  | n :: rest =>
    simp only [runsList]
    rw [runsList_acc _ rest, runsList_acc (runsOne #[] n) rest, runsOne_acc acc n, Array.append_assoc]
end

private theorem shapeOne_acc (fs : FontSet) (pos : Option (Sp × RunShape)) (acc : Array (Node Shaped))
    (n : Node Run) : shapeOne fs pos acc n = acc ++ shapeOne fs pos #[] n := by
  cases n <;> (try cases pos) <;> simp [shapeOne]

private theorem shapeFrom_acc (fs : FontSet) (shapes : Array (Option (Run × RunShape))) (starts : Array Sp)
    (i : Nat) (acc : Array (Node Shaped)) (xs : List (Node Run)) :
    shapeFrom fs shapes starts i acc xs = acc ++ shapeFrom fs shapes starts i #[] xs := by
  induction xs generalizing i acc with
  | nil => simp [shapeFrom]
  | cons n rest ih =>
    simp only [shapeFrom]
    rw [ih, ih (i + 1) (shapeOne fs _ #[] n), shapeOne_acc, Array.append_assoc]

private theorem shapedTexts_append (a b : List (Node Shaped)) :
    shapedTextsList #[] (a ++ b) = shapedTextsList #[] a ++ shapedTextsList #[] b := by
  induction a with
  | nil => simp [shapedTextsList]
  | cons n rest ih =>
    simp only [List.cons_append, shapedTextsList]
    rw [shapedTextsList_acc, ih, shapedTextsList_acc (shapedTextsOne #[] n) rest, Array.append_assoc]

mutual
private theorem texts_shapeOne (fs : FontSet) (pos : Option (Sp × RunShape)) (n : Node Run) :
    shapedTextsList #[] (shapeOne fs pos #[] n).toList = (runsOne #[] n).map (·.text) := by
  cases n with
  | label r => cases pos <;> simp [shapeOne, shapedTextsList, shapedTextsOne, runsOne, placeRun]
  | group xf c a kids =>
    simp only [shapeOne, runsOne, List.push_toArray, List.nil_append, shapedTextsList, shapedTextsOne]
    rw [shapedTextsList_acc, texts_shapeFrom]
    simp
  | draw _ _ _ => simp [shapeOne, shapedTextsList, shapedTextsOne, runsOne]
  | use _ _ => simp [shapeOne, shapedTextsList, shapedTextsOne, runsOne]
  | stamp _ _ _ _ => simp [shapeOne, shapedTextsList, shapedTextsOne, runsOne]
  | image _ _ => simp [shapeOne, shapedTextsList, shapedTextsOne, runsOne]
  | words _ => simp [shapeOne, shapedTextsList, shapedTextsOne, runsOne]
private theorem texts_shapeFrom (fs : FontSet) (shapes : Array (Option (Run × RunShape))) (starts : Array Sp)
    (i : Nat) (xs : List (Node Run)) :
    shapedTextsList #[] (shapeFrom fs shapes starts i #[] xs).toList = (runsList #[] xs).map (·.text) := by
  match xs with
  | [] => simp [shapeFrom, shapedTextsList, runsList]
  | n :: rest =>
    simp only [shapeFrom, runsList]
    rw [shapeFrom_acc, Array.toList_append, shapedTexts_append, texts_shapeOne, texts_shapeFrom,
      runsList_acc (runsOne #[] n) rest, Array.map_append]
end

/-- **Shaping keeps every word a figure's runs carry, in order** (`_text`):
the texts the shaped figure's runs carry — its nodes', and each symbol
body's — are its runs' texts, one for one; shaping adds no run and drops
none. It is a statement about the words a shaped run says, not about the
glyphs that set them: which characters a face draws is shaping's choice,
and a character no face covers is named (`ShapeNotes.missing`, W0609)
rather than set — that the glyphs spell the text less those is pending
work, held meanwhile by the artifact tier's reading of every corpus form. -/
public theorem shapeFigure_text (fs : FontSet) (fig : Figure Run) :
    shapedTextsList #[] (shapeFigure fs fig).1.nodes.toList = (runsList #[] fig.nodes.toList).map (·.text) ∧
    (shapeFigure fs fig).1.symbols.map (fun b => shapedTextsList #[] b.toList) =
      fig.symbols.map (fun b => (runsList #[] b.toList).map (·.text)) := by
  refine ⟨?_, ?_⟩
  · simp only [shapeFigure, shapeList]
    exact texts_shapeFrom fs _ _ 0 fig.nodes.toList
  · simp only [shapeFigure, Array.map_map]
    apply Array.map_congr_left
    intro b _
    simp only [Function.comp_apply, shapeList]
    exact texts_shapeFrom fs _ _ 0 b.toList

/-- Every store entry's vector figure shaped in the document's faces: the
one value both backends read (`Image.Store.shaped`). -/
public def shapeStore (fs : FontSet) (imgs : Image.Store) : Array (Option (Figure Shaped)) :=
  imgs.entries.map fun en => en.vector.map fun fig => (shapeFigure fs fig).1

/-- Every scalar the store's drawn figures set: what joins the per-scalar
fallback the font assembly precomputes, beside the body's. -/
public def storeScalars (imgs : Image.Store) : Array Char :=
  imgs.entries.foldl (fun acc en => match en.vector with
    | some fig =>
      let runs := fig.symbols.foldl (fun a s => runsList a s.toList) (runsList #[] fig.nodes.toList)
      runs.foldl (fun acc r => r.text.toList.foldl (fun a c => if a.contains c then a else a.push c) acc) acc
    | none => acc) #[]

/-- Four hex digits at least, upper case: the code point spelling the
glyph diagnostics use. -/
private def hex4 (n : Nat) : String :=
  let s := String.ofList ((Nat.toDigits 16 n).map Char.toUpper)
  (if s.length < 4 then "".pushn '0' (4 - s.length) else "") ++ s

/-- Every store entry's figure shaped, with what the shaping reports, one
diagnostic per family the document's roles do not answer (N0026), per
substitution (W0009) and per scalar no face covers — a figure loss
(W0609), the engine's drawing shipping without it — each with the figure as
its subject's anchor and beside the source the document names the figure
by — where its span is found. -/
public def shapeStoreNotesBy (fs : FontSet) (imgs : Image.Store) :
    Array (Option (Figure Shaped)) × Array (String × Diag) :=
  imgs.entries.foldl (fun (out, diags) en =>
    match en.vector with
    | some fig =>
      let (sh, notes) := shapeFigure fs fig
      let src := if en.href.isEmpty then en.src else en.href
      let sans := (fs.get (fs.lookup 1 400 false)).family
      let fams := notes.families.map fun f => FigureLoss.svgFontDiag src f sans
      let substs := notes.substs.map fun (idx, c, fb) =>
        Diag.of .W0009 s!"'{(fs.get idx).family}' has no glyph for U+{hex4 c.toNat}"
          (output := FigureLoss.shipsIn en.moving)
          (recovery := some (.replacedBy s!"a glyph from '{(fs.get fb).family}'"))
          (subject := some s!"svg:glyph:{src}:{hex4 c.toNat}")
      let missing := notes.missing.map fun c => FigureLoss.svgGlyphDiag en.moving src (hex4 c.toNat)
      (out.push (some sh), diags ++ (fams ++ substs ++ missing).map (en.src, ·))
    | none => (out.push none, diags)) (#[], #[])

/-- `shapeStoreNotesBy` without the sources. -/
public def shapeStoreNotes (fs : FontSet) (imgs : Image.Store) :
    Array (Option (Figure Shaped)) × Array Diag :=
  let r := shapeStoreNotesBy fs imgs
  (r.1, r.2.map (·.2))

end LeanTex.Core.Layout
