module

public import LeanTex.Core.Elab
public import LeanTex.Core.Picture
public import LeanTex.Core.PictureCensus
import all LeanTex.Core.Elab
import all LeanTex.Core.Diag

namespace LeanTex.Core.Elab

open LeanTex.Core Parse Ir

/-- An unread setting from the actual prepared configuration, with all
earlier definitions in force. The prefix is input provenance, not a list
of reporting events. Empty, repeated and shadowed definitions are allowed. -/
@[expose] public def UnreadPictureSetting (sets : Array (Pos × Array Raw)) (key : String) : Prop :=
  ∃ before setting after,
    sets.toList = before ++ setting :: after ∧
    key ∈ Picture.unreadKeys (before.foldl pictureSettingStyles [])
      (Picture.ofRaws setting.2)

/-- The diagnostic identity the picture loss census reads. -/
@[expose] public def PictureKeyNamed (ds : Array Diag) (key : String) : Prop :=
  ∃ d ∈ ds, d.kind = .W0334 ∧ d.subject = some ("picture:set:" ++ key)

/-- Reading the actual loop as a fold is a proof equation; the production
operation remains the loop over the setting's unread keys. -/
private theorem pictureSettingState_run_exact (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt) (setting : Pos × Array Raw) :
    pictureSettingState ctx acc setting =
      (pictureSettingStyles acc.1 setting,
       (Picture.unreadKeys acc.1 (Picture.ofRaws setting.2)).foldl
         (pictureKeyState ctx setting.1) acc.2) := by
  simp [pictureSettingState, Array.forIn_pure_yield_eq_foldl]

private theorem reportPictureKeys_run_exact (ctx : Ctx) (sets : Array (Pos × Array Raw))
    (st : ESt) :
    reportPictureKeys ctx sets st = (sets.foldl (pictureSettingState ctx) ([], st)).2 := by
  simp [reportPictureKeys, Array.forIn_pure_yield_eq_foldl]

/-- The reporting prefix interprets exactly the style table the drawing
starts from; it does not approximate or reset earlier definitions. -/
private theorem pictureSettingStyles_drawer_agree (before : List (Pos × Array Raw)) :
    before.foldl pictureSettingStyles [] =
      Picture.documentStyles (before.toArray.map (fun setting => Picture.ofRaws setting.2)) := by
  simp [Picture.documentStyles, Array.forIn_pure_yield_eq_foldl, List.foldl_map]
  rfl

private theorem keyState_preserves (ctx : Ctx) (pos : Pos) (st : ESt)
    (key old : String) (h : PictureKeyNamed st.diags old) :
    PictureKeyNamed (pictureKeyState ctx pos st key).diags old := by
  rcases h with ⟨d, hd, hk, hs⟩
  refine ⟨d, ?_, hk, hs⟩
  rw [pictureKeyState, warnOnceState_diags_exact]
  exact Array.mem_push.mpr (Or.inl hd)

private theorem keyState_names (ctx : Ctx) (pos : Pos) (st : ESt) (key : String) :
    PictureKeyNamed (pictureKeyState ctx pos st key).diags key := by
  unfold PictureKeyNamed
  rw [pictureKeyState, warnOnceState_diags_exact]
  exact ⟨_, Array.mem_push_self, warnOnceDiag_kind_exact .., warnOnceDiag_subject_exact ..⟩

private theorem keyFold_preserves (ctx : Ctx) (pos : Pos) (keys : List String)
    (st : ESt) (key : String) (h : PictureKeyNamed st.diags key) :
    PictureKeyNamed (keys.foldl (pictureKeyState ctx pos) st).diags key := by
  induction keys generalizing st with
  | nil => exact h
  | cons k rest ih => exact ih _ (keyState_preserves ctx pos st k key h)

private theorem keyFold_names (ctx : Ctx) (pos : Pos) (keys : List String)
    (st : ESt) (key : String) (h : key ∈ keys) :
    PictureKeyNamed (keys.foldl (pictureKeyState ctx pos) st).diags key := by
  induction keys generalizing st with
  | nil => simp at h
  | cons k rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact keyFold_preserves ctx pos rest _ key (keyState_names ctx pos st key)
    · exact ih _ h

private theorem settingState_preserves (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt) (setting : Pos × Array Raw)
    (key : String) (h : PictureKeyNamed acc.2.diags key) :
    PictureKeyNamed (pictureSettingState ctx acc setting).2.diags key := by
  rw [pictureSettingState_run_exact]
  rw [← Array.foldl_toList]
  exact keyFold_preserves ctx setting.1 _ acc.2 key h

private theorem settingState_names (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt) (setting : Pos × Array Raw)
    (key : String) (h : key ∈ Picture.unreadKeys acc.1 (Picture.ofRaws setting.2)) :
    PictureKeyNamed (pictureSettingState ctx acc setting).2.diags key := by
  rw [pictureSettingState_run_exact]
  rw [← Array.foldl_toList]
  exact keyFold_names ctx setting.1 _ acc.2 key (Array.mem_toList_iff.mpr h)

private theorem settingFold_preserves (ctx : Ctx) (sets : List (Pos × Array Raw))
    (acc : List (String × Array Picture.Tok) × ESt)
    (key : String) (h : PictureKeyNamed acc.2.diags key) :
    PictureKeyNamed (sets.foldl (pictureSettingState ctx) acc).2.diags key := by
  induction sets generalizing acc with
  | nil => exact h
  | cons setting rest ih => exact ih _ (settingState_preserves ctx acc setting key h)

/-- Progress-indexed state equation: after this exact input prefix, the
reporter holds the interpretation of that prefix and no later definition. -/
private theorem settingFold_styles (ctx : Ctx) (sets : List (Pos × Array Raw))
    (acc : List (String × Array Picture.Tok) × ESt) :
    (sets.foldl (pictureSettingState ctx) acc).1 =
      sets.foldl pictureSettingStyles acc.1 := by
  induction sets generalizing acc with
  | nil => rfl
  | cons setting rest ih =>
    simp only [List.foldl_cons, ih, pictureSettingState_run_exact]

/-- Every unread key from every prepared setting is named, with the same
earlier style environment the renderer uses. Repetition only demotes a
site; it never removes the site's structured identity. -/
public theorem reportPictureKeys_named (ctx : Ctx) (sets : Array (Pos × Array Raw))
    (st : ESt) (key : String) (h : UnreadPictureSetting sets key) :
    PictureKeyNamed (reportPictureKeys ctx sets st).diags key := by
  rcases h with ⟨before, setting, after, hsets, hkey⟩
  rw [reportPictureKeys_run_exact, ← Array.foldl_toList, hsets, List.foldl_append,
    List.foldl_cons]
  apply settingFold_preserves
  apply settingState_names
  simpa only [settingFold_styles] using hkey

public theorem finishPictureKeys_named (report : PictureReportContext) (doc : Doc)
    (sets : Array (Pos × Array Raw)) (st : ESt) (key : String)
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

/-- The public prepared-frontend tail preserves the setting's code and
subject through attribution, document judges and site tallying. -/
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

/-- The actual prepared run: an engine picture in the returned document
forces accounting for every unread key of its prepared configuration. -/
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

-- The equations above are the interface across the body interpreter.
-- Finalization must not unfold that recursive interpreter while reducing
-- the small withdrawal selection around it.
attribute [local irreducible] runPrepared prepare prepareExecuted

/-- Source erasure and the final reference judge preserve the diagnostic
identity of the prepared run selected by boundary withdrawal. -/
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

/-- The file-free frontend's complete picture-key guarantee. It quantifies
over the configuration actually prepared for this run, including any
number of earlier style definitions, rather than assuming the source
census survives expansion unchanged. -/
public theorem pictureKeys_named (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (key : String)
    (hdrew : 0 < enginePictures (runRaws file raws earlier metric).1.body)
    (h : UnreadPictureSetting (prepare file raws).picSets key) :
    (runRaws file raws earlier metric).2.any (fun d =>
      d.kind == .W0334 && d.subject == some ("picture:set:" ++ key)) = true := by
  rcases runPreparedFinal_pictureKeys_named file (prepare file raws) earlier metric key
    hdrew h with ⟨d, hd, hk, hs⟩
  exact Array.any_eq_true'.mpr ⟨d, hd, by simp only [hk, hs, BEq.rfl]; rfl⟩

/-- The same guarantee for the production path whose inputs were fulfilled
through `executeInputs`. Both public paths use the same prepared runner. -/
public theorem runExecuted_pictureKeys_named (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (key : String)
    (hdrew : 0 < enginePictures (runExecuted file executed earlier metric).1.body)
    (h : UnreadPictureSetting (prepareExecuted file executed).picSets key) :
    PictureKeyNamed (runExecuted file executed earlier metric).2 key :=
  runPreparedFinal_pictureKeys_named file (prepareExecuted file executed) earlier metric key
    hdrew h

end LeanTex.Core.Elab
