module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Font
public import LeanTex.Core.Diag
public import LeanTex.Core.Image
public import LeanTex.Core.LayoutFigure
import LeanTex.Core.FigureOutline
public import LeanTex.Core.FigureLoss

/-!
# The store a document's drawn figures ride in

The driver's SVG route answers each image request with the figure the
engine draws, if it draws one, and whether its source moves. Two steps put
those answers where layout and both backends read them, and every caller —
the driver, the tiers, the suite — takes these two, never a copy of them:
`attach` hangs each answer on its store entry, and `settle` sets every
drawn figure's text in the document's settled faces and gives a moving
figure its still face.
-/

namespace LeanTex.Core.FigureStore

open LeanTex.Core

/-- One request's answer from the SVG route: the figure the engine draws —
none where the converter drew it, or nothing did — whether the source
moves, and the figure's rasters planned, one per raster in order. -/
public structure Drawn where
  vector : Option (Gfx.Figure Gfx.Run)
  moving : Bool
  plans : Array Image.Plan

/-- **A drawn figure's rasters, planned**: each raster's bytes through the
planner every included PNG and JPEG takes (`Image.probe`, `Image.plan`),
so the PDF embeds a figure's raster as it embeds a page's. A raster the
planner refuses leaves the figure without its rasters, the drop one of its
named losses (`FigureLoss.unrastered`). -/
public def rasterPlans (params : Image.PlanParams) (fig : Gfx.Figure Gfx.Run) :
    Gfx.Figure Gfx.Run × Array Image.Plan :=
  let plans := fig.rasters.map fun r => Image.probe r.bytes >>= Image.plan params
  if plans.all (·.isOk) then (fig, plans.filterMap (·.toOption))
  else (FigureLoss.unrastered fig, #[])

private theorem filterMap_ok_length {α : Type} (l : List (Except String α))
    (h : ∀ x ∈ l, x.isOk = true) : (l.filterMap (·.toOption)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    have hx := h x (by simp)
    have hr := ih fun y hy => h y (by simp [hy])
    cases x with
    | error e => simp [Except.isOk, Except.toBool] at hx
    | ok a =>
      show (a :: List.filterMap (fun x => x.toOption) rest).length = (Except.ok a :: rest).length
      simp only [List.length_cons, hr]

/-- **One plan per raster** (`_exact`): whatever the planner answers, the
plans `rasterPlans` returns number the rasters of the figure it returns —
every raster planned, or no raster and no plan — so each raster a store
entry names has its own (`slotRasters`). -/
public theorem rasterPlans_exact (params : Image.PlanParams) (fig : Gfx.Figure Gfx.Run) :
    (rasterPlans params fig).2.size = (rasterPlans params fig).1.rasters.size := by
  unfold rasterPlans
  dsimp only
  split
  · next h =>
    rw [Array.all_eq_true_iff_forall_mem] at h
    rw [← Array.length_toList, Array.toList_filterMap, filterMap_ok_length _ (fun x hx => h x (by simpa using hx)),
      Array.length_toList, Array.size_map]
  · simp only [FigureLoss.unrastered_rasters, Array.size_empty]

/-- A drawn figure's rasters as entries of their own after `entries`: one
per plan, owned by the figure's entry `k`, each smoothed where its raster
may be, and the figure's entry naming them. A figure without rasters, or
one that did not load, adds none. -/
public def slotRasters (entries : Array Image.Loaded) (k : Nat) (plans : Array Image.Plan) :
    Array Image.Loaded :=
  match entries[k]? with
  | some en =>
    if en.info.isNone || en.vector.isNone || plans.isEmpty then entries else
    let slots := (Array.range plans.size).map (entries.size + ·)
    let smooth (r : Nat) : Bool := ((en.vector.bind (·.rasters[r]?)).map (·.smooth)).getD false
    let owned := plans.zipIdx.map fun (p, r) =>
      ({ toRequest := en.toRequest, info := some p, rasterOf := some k, interpolate := smooth r } :
        Image.Loaded)
    (entries.modify k fun e => { e with rasterSlots := slots }) ++ owned
  | none => entries

/-- **Each request's drawn figure on its entry**: an entry that loaded is
the figure's, an entry that did not keeps none, so layout sizes a drawn
figure by its own box and both backends draw the one value. A drawn
figure's rasters follow every request's entry, each an entry of its own
(`slotRasters`), so the request entries keep their places. -/
public def attach (store : Image.Store) (drawn : Array (Option Drawn)) : Image.Store :=
  let entries := store.entries.mapIdx fun k en =>
    match (drawn[k]?).join with
    | some d => if en.info.isSome then { en with vector := d.vector, moving := d.moving } else en
    | none => en
  let n := store.entries.size
  { store with entries := (Array.range n).foldl (fun es k =>
      match (drawn[k]?).join with
      | some d => slotRasters es k d.plans
      | none => es) entries }

/-- **Every drawn figure set in the settled faces** (`Layout.shapeStoreNotes`),
and a moving figure's still face — print and reduced motion — the engine's
drawing of the pose the PDF draws, its text the faces' outlines. Each note
the shaping owes comes with the source of the entry it is about, which is
where the document names the figure. -/
public def settle (fs : Font.FontSet) (store : Image.Store) : Image.Store × Array (String × Diag) :=
  let (shaped, notes) := Layout.shapeStoreNotesBy fs store
  let entries := store.entries.mapIdx fun k en =>
    match (shaped[k]?).join with
    | some fig => if en.moving then { en with posterSvg := some (FigureOutline.poster fs fig).toUTF8 } else en
    | none => en
  ({ store with entries, shaped }, notes)

end LeanTex.Core.FigureStore
