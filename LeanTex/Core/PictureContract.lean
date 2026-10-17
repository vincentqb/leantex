module

public import LeanTex.Core.Elab
public import LeanTex.Core.Picture
public import LeanTex.Core.PictureCensus
import all LeanTex.Core.Elab
import all LeanTex.Core.Diag

namespace LeanTex.Core.Elab

open LeanTex.Core Parse Ir

/-- An unread setting key of the prepared configuration, with every earlier definition in force. -/
@[expose] public def UnreadPictureSetting (sets : Array (Span × Array Raw)) (key : String) : Prop :=
  ∃ before setting after,
    sets.toList = before ++ setting :: after ∧
    key ∈ Picture.unreadKeys (before.foldl pictureSettingStyles [])
      (Picture.ofSetting setting)

/-- The diagnostic identity the picture loss census reads. -/
@[expose] public def PictureKeyNamed (ds : Array Diag) (key : String) : Prop :=
  ∃ d ∈ ds, d.kind = .W0334 ∧ d.subject = some ("picture:set:" ++ key)

private theorem pictureSettingState_run_exact (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt) (setting : Span × Array Raw) :
    pictureSettingState ctx acc setting =
      (pictureSettingStyles acc.1 setting,
       (Picture.unreadKeys acc.1 (Picture.ofSetting setting)).foldl
         (pictureKeyState ctx setting.1) acc.2) := by
  simp [pictureSettingState, Array.forIn_pure_yield_eq_foldl]

private theorem reportPictureKeys_run_exact (ctx : Ctx) (sets : Array (Span × Array Raw))
    (st : ESt) :
    reportPictureKeys ctx sets st = (sets.foldl (pictureSettingState ctx) ([], st)).2 := by
  simp [reportPictureKeys, Array.forIn_pure_yield_eq_foldl]

private theorem pictureSettingStyles_drawer_agree (before : List (Span × Array Raw)) :
    before.foldl pictureSettingStyles [] =
      Picture.documentStyles (before.toArray.map Picture.ofSetting) := by
  simp [Picture.documentStyles, Array.forIn_pure_yield_eq_foldl, List.foldl_map]
  rfl

private theorem keyState_preserves (ctx : Ctx) (site : Span) (st : ESt)
    (key old : String) (h : PictureKeyNamed st.diags old) :
    PictureKeyNamed (pictureKeyState ctx site st key).diags old := by
  rcases h with ⟨d, hd, hk, hs⟩
  refine ⟨d, ?_, hk, hs⟩
  rw [pictureKeyState, warnOnceState_diags_exact]
  exact Array.mem_push.mpr (Or.inl hd)

private theorem keyState_names (ctx : Ctx) (site : Span) (st : ESt) (key : String) :
    PictureKeyNamed (pictureKeyState ctx site st key).diags key := by
  unfold PictureKeyNamed
  rw [pictureKeyState, warnOnceState_diags_exact]
  exact ⟨_, Array.mem_push_self, warnOnceDiag_kind_exact .., warnOnceDiag_subject_exact ..⟩

private theorem keyFold_preserves (ctx : Ctx) (site : Span) (keys : List String)
    (st : ESt) (key : String) (h : PictureKeyNamed st.diags key) :
    PictureKeyNamed (keys.foldl (pictureKeyState ctx site) st).diags key := by
  induction keys generalizing st with
  | nil => exact h
  | cons k _ ih => exact ih _ (keyState_preserves ctx site st k key h)

private theorem keyFold_names (ctx : Ctx) (site : Span) (keys : List String)
    (st : ESt) (key : String) (h : key ∈ keys) :
    PictureKeyNamed (keys.foldl (pictureKeyState ctx site) st).diags key := by
  induction keys generalizing st with
  | nil => simp at h
  | cons k rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact keyFold_preserves ctx site rest _ key (keyState_names ctx site st key)
    · exact ih _ h

private theorem settingState_preserves (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt) (setting : Span × Array Raw)
    (key : String) (h : PictureKeyNamed acc.2.diags key) :
    PictureKeyNamed (pictureSettingState ctx acc setting).2.diags key := by
  rw [pictureSettingState_run_exact]
  rw [← Array.foldl_toList]
  exact keyFold_preserves ctx setting.1 _ acc.2 key h

private theorem settingState_names (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt) (setting : Span × Array Raw)
    (key : String) (h : key ∈ Picture.unreadKeys acc.1 (Picture.ofSetting setting)) :
    PictureKeyNamed (pictureSettingState ctx acc setting).2.diags key := by
  rw [pictureSettingState_run_exact]
  rw [← Array.foldl_toList]
  exact keyFold_names ctx setting.1 _ acc.2 key (Array.mem_toList_iff.mpr h)

private theorem settingFold_preserves (ctx : Ctx) (sets : List (Span × Array Raw))
    (acc : List (String × Array Picture.Tok) × ESt)
    (key : String) (h : PictureKeyNamed acc.2.diags key) :
    PictureKeyNamed (sets.foldl (pictureSettingState ctx) acc).2.diags key := by
  induction sets generalizing acc with
  | nil => exact h
  | cons setting _ ih => exact ih _ (settingState_preserves ctx acc setting key h)

private theorem settingFold_styles (ctx : Ctx) (sets : List (Span × Array Raw))
    (acc : List (String × Array Picture.Tok) × ESt) :
    (sets.foldl (pictureSettingState ctx) acc).1 =
      sets.foldl pictureSettingStyles acc.1 := by
  induction sets generalizing acc with
  | nil => rfl
  | cons setting rest ih =>
    simp only [List.foldl_cons, ih, pictureSettingState_run_exact]

public theorem reportPictureKeys_named (ctx : Ctx) (sets : Array (Span × Array Raw))
    (st : ESt) (key : String) (h : UnreadPictureSetting sets key) :
    PictureKeyNamed (reportPictureKeys ctx sets st).diags key := by
  rcases h with ⟨before, setting, after, hsets, hkey⟩
  rw [reportPictureKeys_run_exact, ← Array.foldl_toList, hsets, List.foldl_append,
    List.foldl_cons]
  apply settingFold_preserves
  apply settingState_names
  simpa only [settingFold_styles] using hkey

public theorem finishPictureKeys_named (report : PictureReportContext) (doc : Doc)
    (sets : Array (Span × Array Raw)) (st : ESt) (key : String)
    (hdrew : 0 < enginePictures doc.body) (h : UnreadPictureSetting sets key) :
    PictureKeyNamed (finishPictureKeys report doc sets st).diags key := by
  rcases reportPictureKeys_named report.ctx sets { st with diags := #[] } key h with
    ⟨d, hd, hk, hs⟩
  refine ⟨d, ?_, hk, hs⟩
  simp only [finishPictureKeys, hdrew, ↓reduceIte, Array.mem_append]
  exact Or.inl (Or.inr hd)

private theorem named_tally (ds : Array Diag) (key : String)
    (h : PictureKeyNamed ds key) : PictureKeyNamed (Diag.tallySites ds) key := by
  rcases h with ⟨d, hd, hk, hs⟩
  rcases Array.mem_iff_getElem.mp hd with ⟨i, hi, he⟩
  rcases Diag.tallySites_id ds i hi with ⟨d', hd', hk', _, _, _, _, hs'⟩
  refine ⟨d', Array.mem_iff_getElem?.mpr ⟨i, hd'⟩, ?_, ?_⟩
  · simpa only [he] using hk'.trans (he ▸ hk)
  · simpa only [he] using hs'.trans (he ▸ hs)

public theorem completePrepared_pictureKeys_named (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) (key : String)
    (hdrew : 0 < enginePictures (completePrepared file p earlier doc table report st).1.body)
    (h : UnreadPictureSetting p.picSets key) :
    PictureKeyNamed (completePrepared file p earlier doc table report st).2.1 key := by
  unfold completePrepared at hdrew ⊢
  dsimp only at hdrew ⊢
  apply named_tally
  rcases finishPictureKeys_named report _ p.picSets st key hdrew h with ⟨d, hd, hk, hs⟩
  refine ⟨p.sourceTriggers.attribute d, ?_, hk, hs⟩
  refine Array.mem_map.mpr ⟨d, ?_, rfl⟩
  apply accountRecovered_mem
  simp only [Array.mem_append, hd, or_true, true_or]

public theorem runPrepared_pictureKeys_named (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (withdrawn : Array String)
    (key : String)
    (hdrew : 0 < enginePictures (runPrepared file p earlier metric withdrawn).1.body)
    (h : UnreadPictureSetting p.picSets key) :
    PictureKeyNamed (runPrepared file p earlier metric withdrawn).2.1 key := by
  rcases runPrepared_complete_exact file p earlier metric withdrawn with
    ⟨doc, table, report, st, heq⟩
  rw [heq] at hdrew ⊢
  exact completePrepared_pictureKeys_named file p earlier doc table report st key hdrew h

-- Finalization must not unfold the recursive interpreter: the equations above are its interface.
attribute [local irreducible] runPrepared prepare prepareExecuted

public theorem runPreparedFinal_pictureKeys_named (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (key : String)
    (hdrew : 0 < enginePictures (runPreparedFinal file p earlier metric).1.body)
    (h : UnreadPictureSetting p.picSets key) :
    PictureKeyNamed (runPreparedFinal file p earlier metric).2 key := by
  let first := runPrepared file p earlier metric
  let chosen := if first.2.2.fallbacks.isEmpty then first
    else runPrepared file p earlier metric first.2.2.fallbacks
  change 0 < enginePictures (Ir.eraseLocations chosen.1).body at hdrew
  rw [eraseLocations_pictureCount_exact] at hdrew
  change PictureKeyNamed (Diag.tallySites (chosen.2.1 ++
    Ir.refDiags chosen.2.2.labels (ReqSpans.spanOf chosen.2.2.refs) chosen.1)) key
  have hchosen : PictureKeyNamed chosen.2.1 key := by
    dsimp only [chosen] at hdrew ⊢
    by_cases hempty : first.2.2.fallbacks.isEmpty = true
    · simp only [hempty, ↓reduceIte] at hdrew ⊢
      exact runPrepared_pictureKeys_named file p earlier metric #[] key hdrew h
    · simp only [hempty] at hdrew ⊢
      exact runPrepared_pictureKeys_named file p earlier metric first.2.2.fallbacks key hdrew h
  apply named_tally
  rcases hchosen with ⟨d, hd, hk, hs⟩
  exact ⟨d, Array.mem_append.mpr (Or.inl hd), hk, hs⟩

public theorem pictureKeys_named (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (key : String)
    (hdrew : 0 < enginePictures (runRaws file raws earlier metric).1.body)
    (h : UnreadPictureSetting (prepare file raws).picSets key) :
    (runRaws file raws earlier metric).2.any (fun d =>
      d.kind == .W0334 && d.subject == some ("picture:set:" ++ key)) = true := by
  rcases runPreparedFinal_pictureKeys_named file (prepare file raws) earlier metric key
    hdrew h with ⟨d, hd, hk, hs⟩
  exact Array.any_eq_true'.mpr ⟨d, hd, by simp only [hk, hs, BEq.rfl]; rfl⟩

public theorem runExecuted_pictureKeys_named (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (key : String)
    (hdrew : 0 < enginePictures (runExecuted file executed earlier metric).1.body)
    (h : UnreadPictureSetting (prepareExecuted file executed).picSets key) :
    PictureKeyNamed (runExecuted file executed earlier metric).2 key :=
  runPreparedFinal_pictureKeys_named file (prepareExecuted file executed) earlier metric key
    hdrew h

end LeanTex.Core.Elab

namespace LeanTex.Core.Ir

public theorem standaloneHead_ten_exact :
    standaloneHead (Dim.pt 10) = "\\documentclass{standalone}\n\\usepackage{tikz}\n" := by
  decide

end LeanTex.Core.Ir

namespace LeanTex.Core.Picture

public theorem shade_stops_exact (s : ShadeSpec) :
    s.stops.map (·.offset.val) = (match s.kind with
      | .axis => #[0, 16384, 32768, 49152, 65536]
      | .radial => #[0, 32768, 65536]
      | .ball => #[0, 11796, 23593, 32768, 65536]) ∧
    s.stops.map (·.color) = (match s.kind with
      | .axis => #[s.bottom, s.bottom, s.middle, s.top, s.top]
      | .radial => #[s.inner, s.outer, s.outer]
      | .ball => #[Ir.Color.mix s.ball 15 Ir.Color.white, Ir.Color.mix s.ball 75 Ir.Color.white,
          Ir.Color.mix s.ball 70 Ir.Color.blackInk, Ir.Color.mix s.ball 50 Ir.Color.blackInk,
          Ir.Color.blackInk]) := by
  cases h : s.kind <;> simp [ShadeSpec.stops, stopAt, h] <;> decide

end LeanTex.Core.Picture
