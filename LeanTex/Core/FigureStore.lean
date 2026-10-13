module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Font
public import LeanTex.Core.Diag
public import LeanTex.Core.Image
public import LeanTex.Core.LayoutFigure
import LeanTex.Core.FigureOutline
public import LeanTex.Core.FigureLoss

/-! Hangs the SVG route's drawn figures on the image store and shapes them in the settled faces. -/

namespace LeanTex.Core.FigureStore

open LeanTex.Core

/-- The SVG route's answer for one request: the engine's figure, whether it moves, and its raster plans. -/
public structure Drawn where
  vector : Option (Gfx.Figure Gfx.Run)
  moving : Bool
  plans : Array Image.Plan

/-- Plans every raster of a figure, or drops all its rasters when the planner refuses one. -/
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

/-- Appends one entry per raster plan, owned by entry `k`, and records their slots on it. -/
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

/-- Attaches each request's drawn figure and its raster entries to the store. -/
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

/-- Shapes every drawn figure in the settled faces and gives a moving figure its still poster. -/
public def settle (fs : Font.FontSet) (store : Image.Store) : Image.Store × Array (String × Diag) :=
  let (shaped, notes) := Layout.shapeStoreNotesBy fs store
  let entries := store.entries.mapIdx fun k en =>
    match (shaped[k]?).join with
    | some fig => if en.moving then { en with posterSvg := some (FigureOutline.poster fs fig).toUTF8 } else en
    | none => en
  ({ store with entries, shaped }, notes)

end LeanTex.Core.FigureStore
