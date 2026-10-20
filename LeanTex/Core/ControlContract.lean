module

public import LeanTex.Core.Elab

import all LeanTex.Core.Elab
import LeanTex.Core.MarginNoteContract
import all LeanTex.Core.Compat
import all LeanTex.Core.Ir
import all LeanTex.Core.Contrast

namespace LeanTex.Core.Elab

open Parse

/-- The production completion after a compatibility checkpoint: text rewrite, body interpreter,
judges, withdrawal and reference diagnostics. -/
public def runRewriteFinal (file : String) (picScan : Compat.BoundaryScan)
    (picMacros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor)
    (attempts : Array Compat.InputAttempt := #[]) (mentions : Array String := #[])
    (stripped : Array Compat.Stripped := #[]) :
    Ir.Doc × Array Diag :=
  runPreparedFinal file
    (prepareRewritten file picScan picMacros triggers priorDiags
      (Compat.finishRewrite cursor) attempts mentions stripped)
    earlier metric

public theorem runExecuted_rewrite_exact (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) :
    runExecuted file executed earlier metric =
      runRewriteFinal file (Compat.boundaryScan file executed.raws) (macroScan executed.raws)
        executed.sourceTriggers (Compat.unusedLengths file executed.raws executed.edefReads) earlier
        metric (Compat.beginRewrite executed) executed.inputAttempts executed.mentions
        executed.stripped := by rfl

/-- The control table's names stand in strictly ascending byte order, so are distinct, clear of
`\cite`, `\appendix` and `\define`, none is spelled as a saved overlay-native name, and none opens or
closes a group primitive. -/
public theorem ctrlRows_sound : Compat.CtrlRowsSound := by
  unfold Compat.CtrlRowsSound
  decide +kernel

/-- At every cursor a row no leave keeps consumes exactly what its signature reads and one lacking a
standing argument or kept is left to elaboration; at a body cursor a quiet row of groups consumes
exactly its group prefix. -/
public theorem ctrl_rows_consumed_contract :
    (∀ row ∈ Compat.ctrlRows, Compat.CtrlRowConsumed row) ∧
    (∀ row ∈ Compat.ctrlRows, row.quiet = true → (∀ k ∈ row.sig, k = .group ∨ k = .needed) →
      Compat.ControlGroupsConsumed row.name row.sig.length) ∧
    (∀ row ∈ Compat.ctrlRows, Compat.CtrlRowDeclines row) ∧
    Compat.UnknownControlPreserved "zzNotAControl" :=
  ⟨Compat.ctrlRow_control_contract ctrlRows_sound,
    fun row hrow hquiet hsig => Compat.ctrlRow_groups_consumed ctrlRows_sound row hrow hquiet hsig,
    Compat.ctrlRow_declines_contract ctrlRows_sound,
    Compat.unknown_control_contract (by decide +kernel)⟩

public theorem ctrlRow_document_exact (file : String) (scan : Compat.BoundaryScan)
    (macros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) (body : Array Raw)
    (row : Compat.CtrlRow) (pos docPos : Pos) (args : Array (Option (Array Raw)))
    (pre taken post : List Raw)
    (hrow : row ∈ Compat.ctrlRows) (hp : cursor.outsidePicture)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body docPos])
    (hb : body.toList = pre ++ .ctrl row.name pos :: (taken ++ post))
    (hpre : Compat.LiteralRaws pre) (hpost : Compat.LiteralRaws post)
    (hk : Compat.argsRead body #[] row.sig (pre.length + 1) =
      some (args, pre.length + 1 + taken.length))
    (hl : cursor.rowStandsInBody row args)
    (attempts : Array Compat.InputAttempt := #[]) (mentions : Array String := #[])
    (stripped : Array Compat.Stripped := #[]) :
    runRewriteFinal file scan macros triggers priorDiags earlier metric cursor attempts mentions
        stripped =
      runPreparedFinal file
        (prepareRewritten file scan macros triggers priorDiags
          (Compat.finishCtrlRowDocument cursor row
            ⟨row.name, pos, args, body, pre.length + 1, pre.length + 1 + taken.length⟩
            docPos pre.toArray post.toArray)
          attempts mentions stripped) earlier metric := by
  unfold runRewriteFinal
  rw [Compat.finishRewrite_row_document_exact ctrlRows_sound cursor body row hrow pos docPos
    args pre taken post hp hs hb hpre hpost hk hl]

public theorem ctrlRow_operands_agree (file : String) (scan : Compat.BoundaryScan)
    (macros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) (left right : Array Raw)
    (row : Compat.CtrlRow) (pos docPos : Pos) (argsLeft argsRight : Array (Option (Array Raw)))
    (pre post takenLeft takenRight : List Raw)
    (hrow : row ∈ Compat.ctrlRows) (hfixed : row.action.reads = false)
    (hp : cursor.outsidePicture)
    (hleft : left.toList = pre ++ .ctrl row.name pos :: (takenLeft ++ post))
    (hright : right.toList = pre ++ .ctrl row.name pos :: (takenRight ++ post))
    (hpre : Compat.LiteralRaws pre) (hpost : Compat.LiteralRaws post)
    (hkleft : Compat.argsRead left #[] row.sig (pre.length + 1) =
      some (argsLeft, pre.length + 1 + takenLeft.length))
    (hkright : Compat.argsRead right #[] row.sig (pre.length + 1) =
      some (argsRight, pre.length + 1 + takenRight.length))
    (attempts : Array Compat.InputAttempt := #[]) (mentions : Array String := #[])
    (stripped : Array Compat.Stripped := #[]) :
    runRewriteFinal file scan macros triggers priorDiags earlier metric
      (cursor.withDocument left docPos) attempts mentions stripped =
    runRewriteFinal file scan macros triggers priorDiags earlier metric
      (cursor.withDocument right docPos) attempts mentions stripped := by
  rw [ctrlRow_document_exact file scan macros triggers priorDiags earlier metric
    (cursor.withDocument left docPos) left row pos docPos argsLeft pre takenLeft post hrow hp rfl
    hleft hpre hpost hkleft (Compat.ctrlLeft_fixed row _ argsLeft hfixed)
    attempts mentions stripped,
    ctrlRow_document_exact file scan macros triggers priorDiags earlier metric
    (cursor.withDocument right docPos) right row pos docPos argsRight pre takenRight post hrow hp
    rfl hright hpre hpost hkright (Compat.ctrlLeft_fixed row _ argsRight hfixed)
    attempts mentions stripped,
    Compat.finishCtrlRowDocument_source_exact, Compat.finishCtrlRowDocument_source_exact,
    Compat.finishCtrlRowDocument_fixed_exact cursor row
      ⟨row.name, pos, argsLeft, left, pre.length + 1, pre.length + 1 + takenLeft.length⟩
      ⟨row.name, pos, argsRight, right, pre.length + 1, pre.length + 1 + takenRight.length⟩
      hfixed rfl]

/-- A recovery accounted by its producer's diagnostic code and its command identity. -/
@[expose] public def RecoveryNamed (ds : Array Diag) (item : Ir.Recovered) : Prop :=
  ∃ d ∈ ds, d.kind = item.code ∧ d.subject = some item.subject

public theorem accountRecoveredItem_named (ds : Array Diag) (item : Ir.Recovered)
    (observed : Array Diag) :
    RecoveryNamed (accountRecoveredItem ds item observed) item := by
  unfold accountRecoveredItem
  split
  · rename_i h
    rcases Array.any_eq_true'.mp h with ⟨d, hd, hs⟩
    exact ⟨d, hd, by
      simpa only [recoveryMatches, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hs⟩
  · dsimp only
    split
    · exact ⟨_, Array.mem_push_self, recoveryDiagnostic_code_exact item,
        recoveryDiagnostic_subject_exact item⟩
    · rename_i h
      have hnonempty : (observed.filter (recoveryMatches item)).isEmpty = false :=
        Bool.eq_false_iff.mpr h
      rcases Array.isEmpty_eq_false_iff_exists_mem.mp hnonempty with ⟨d, hd⟩
      exact ⟨d, Array.mem_append.mpr (Or.inr hd), by
        simpa only [recoveryMatches, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using
          (Array.mem_filter.mp hd).2⟩

private theorem recoveryFold_preserves (items : List Ir.Recovered)
    (observed ds : Array Diag) (item : Ir.Recovered) (h : RecoveryNamed ds item) :
    RecoveryNamed
      (items.foldl (fun ds item => accountRecoveredItem ds item observed) ds) item := by
  induction items generalizing ds with
  | nil => exact h
  | cons x xs ih =>
    rcases h with ⟨d, hd, hs⟩
    exact ih _ ⟨d, accountRecoveredItem_mem ds x observed d hd, hs⟩

private theorem recoveryFold_names (items : List Ir.Recovered)
    (observed ds : Array Diag) (item : Ir.Recovered) (h : item ∈ items) :
    RecoveryNamed
      (items.foldl (fun ds item => accountRecoveredItem ds item observed) ds) item := by
  induction items generalizing ds with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact recoveryFold_preserves xs observed _ item
        (accountRecoveredItem_named ds item observed)
    · exact ih _ h

public theorem accountRecovered_named (items : Array Ir.Recovered) (ds observed : Array Diag)
    (item : Ir.Recovered) (h : item ∈ items) :
    RecoveryNamed (accountRecovered items ds observed) item := by
  rw [accountRecovered_run_exact, ← Array.foldl_toList]
  exact recoveryFold_names items.toList observed ds item (Array.mem_toList_iff.mpr h)

private theorem recoveryFold_existing (items : List Ir.Recovered) (observed ds : Array Diag)
    (h : ∀ item ∈ items, ds.any (recoveryMatches item) = true) :
    items.foldl (fun ds item => accountRecoveredItem ds item observed) ds = ds := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.foldl_cons, accountRecoveredItem, h item List.mem_cons_self, ↓reduceIte]
    exact ih (fun item hi => h item (List.mem_cons_of_mem _ hi))

public theorem accountRecovered_fixed_point (items : Array Ir.Recovered) (ds observed : Array Diag)
    (h : ∀ item ∈ items, ds.any (recoveryMatches item) = true) :
    accountRecovered items ds observed = ds := by
  rw [accountRecovered_run_exact, ← Array.foldl_toList]
  exact recoveryFold_existing items.toList observed ds
    (fun item hi => h item (Array.mem_toList_iff.mp hi))

private theorem recovery_tally (ds : Array Diag) (item : Ir.Recovered)
    (h : RecoveryNamed ds item) : RecoveryNamed (Diag.tallySites ds) item := by
  rcases h with ⟨d, hd, hk, hs⟩
  rcases Array.mem_iff_getElem.mp hd with ⟨i, hi, he⟩
  rcases Diag.tallySites_id ds i hi with ⟨d', hd', hk', _, _, _, _, hs'⟩
  exact ⟨d', Array.mem_iff_getElem?.mpr ⟨i, hd'⟩,
    hk'.trans (he ▸ hk), hs'.trans (he ▸ hs)⟩

public theorem completePrepared_recovery_named (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) (item : Ir.Recovered)
    (h : item ∈ (completePrepared file p earlier doc table report st).1.salvage) :
    RecoveryNamed (completePrepared file p earlier doc table report st).2.1 item := by
  unfold completePrepared at h ⊢
  dsimp only at h ⊢
  apply recovery_tally
  rcases accountRecovered_named _ _ _ item h with ⟨d, hd, hk, hs⟩
  exact ⟨p.sourceTriggers.attribute d, Array.mem_map.mpr ⟨d, hd, rfl⟩, hk, hs⟩

public theorem runPrepared_recovery_named (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (withdrawn : Array String)
    (item : Ir.Recovered)
    (h : item ∈ (runPrepared file p earlier metric withdrawn).1.salvage) :
    RecoveryNamed (runPrepared file p earlier metric withdrawn).2.1 item := by
  rcases runPrepared_complete_exact file p earlier metric withdrawn with
    ⟨doc, table, report, st, heq⟩
  rw [heq] at h ⊢
  exact completePrepared_recovery_named file p earlier doc table report st item h

attribute [local irreducible] runPrepared prepare prepareExecuted

public theorem runPreparedFinal_recovery_named (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (item : Ir.Recovered)
    (h : item ∈ (runPreparedFinal file p earlier metric).1.salvage) :
    RecoveryNamed (runPreparedFinal file p earlier metric).2 item := by
  let first := runPrepared file p earlier metric
  let chosen := if first.2.2.fallbacks.isEmpty then first
    else runPrepared file p earlier metric first.2.2.fallbacks
  change item ∈ chosen.1.salvage at h
  change RecoveryNamed (Diag.tallySites (chosen.2.1 ++
    Ir.refDiags chosen.2.2.labels (ReqSpans.spanOf chosen.2.2.refs) chosen.1)) item
  have hchosen : RecoveryNamed chosen.2.1 item := by
    dsimp only [chosen] at h ⊢
    by_cases hempty : first.2.2.fallbacks.isEmpty = true
    · simp only [hempty, ↓reduceIte] at h ⊢
      exact runPrepared_recovery_named file p earlier metric #[] item h
    · simp only [hempty] at h ⊢
      exact runPrepared_recovery_named file p earlier metric first.2.2.fallbacks item h
  apply recovery_tally
  rcases hchosen with ⟨d, hd, hs⟩
  exact ⟨d, Array.mem_append.mpr (Or.inl hd), hs⟩

public theorem runRaws_recovery_named (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (item : Ir.Recovered)
    (h : item ∈ (runRaws file raws earlier metric).1.salvage) :
    (runRaws file raws earlier metric).2.any (·.subject == some item.subject) = true := by
  rcases runPreparedFinal_recovery_named file (prepare file raws) earlier metric item h with
    ⟨d, hd, _, hs⟩
  exact Array.any_eq_true'.mpr ⟨d, hd, by simp only [hs, BEq.rfl]⟩

public theorem runExecuted_recovery_named (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (item : Ir.Recovered)
    (h : item ∈ (runExecuted file executed earlier metric).1.salvage) :
    RecoveryNamed (runExecuted file executed earlier metric).2 item :=
  runPreparedFinal_recovery_named file (prepareExecuted file executed) earlier metric item h

public theorem run_recovery_named (file input : String) (item : Ir.Recovered)
    (h : item ∈ (run file input).1.salvage) :
    (run file input).2.any (·.subject == some item.subject) = true :=
  runRaws_recovery_named file _ _ _ item h

public theorem completePrepared_doc_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) :
    (completePrepared file p earlier doc table report st).1 = doc := by
  unfold completePrepared
  rfl

public theorem completePrepared_body_text (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) :
    Ir.blocksText (completePrepared file p earlier doc table report st).1.body =
      Ir.blocksText doc.body := by
  rw [completePrepared_doc_exact]

/-- The recovered-word input condition, checked on the real prepared context and body. -/
@[expose] public def PreparedRecoveryWord (file : String) (p : Prepared) (metric : Ir.Pic.LabelMetric)
    (word : String) : Prop :=
  ∀ withdrawn,
    let entry := preparedBody file p metric withdrawn
    RecoveryWordInput entry.1.ctx entry.1.raws word

public theorem runPrepared_recovered_word_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (withdrawn : Array String)
    (word : String)
    (h : RecoveryWordInput (preparedBody file p metric withdrawn).1.ctx
      (preparedBody file p metric withdrawn).1.raws word) :
    Ir.blocksText (runPrepared file p earlier metric withdrawn).1.body = word := by
  rw [runPrepared_body_exact]
  dsimp only
  have hb := runDocBody_recovered_word_exact
    (preparedBody file p metric withdrawn).1 (preparedBody file p metric withdrawn).2 word h
  cases hx : (runDocBody (preparedBody file p metric withdrawn).1).run
      (preparedBody file p metric withdrawn).2 with
  | mk result st =>
    obtain ⟨doc, table, report⟩ := result
    simp only [hx] at hb
    have he : StateT.run (do
          let r ← runDocBody (preparedBody file p metric withdrawn).1
          settleDocMargins r) (preparedBody file p metric withdrawn).2 =
        (settleDocMargins (doc, table, report)).run st := by
      rw [StateT.run_bind, hx]; rfl
    rw [he]
    generalize hy : (settleDocMargins (doc, table, report)).run st = y
    obtain ⟨⟨doc', table', report'⟩, st'⟩ := y
    have hd : doc'.body = (MarginNote.settle (0 < doc.page.marginPar.width) doc.body).1 := by
      have := settleDocMargins_body (doc, table, report) st
      rw [hy] at this
      exact this
    simp only
    rw [completePrepared_body_text, hd, MarginNote.settle_text]
    exact hb

public theorem runPreparedFinal_recovered_word_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (word : String)
    (h : PreparedRecoveryWord file p metric word) :
    Ir.blocksText (runPreparedFinal file p earlier metric).1.body = word := by
  let first := runPrepared file p earlier metric
  let chosen := if first.2.2.fallbacks.isEmpty then first
    else runPrepared file p earlier metric first.2.2.fallbacks
  change Ir.blocksText (Ir.eraseLocations chosen.1).body = word
  rw [show Ir.blocksText (Ir.eraseLocations chosen.1).body =
    Ir.blocksText chosen.1.body from congrArg Prod.fst (Ir.eraseLocations_text chosen.1)]
  dsimp only [chosen]
  split
  · exact runPrepared_recovered_word_exact file p earlier metric #[] word (h #[])
  · exact runPrepared_recovered_word_exact file p earlier metric first.2.2.fallbacks
      word (h first.2.2.fallbacks)

public theorem runExecuted_recovered_word_contract (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (word : String)
    (h : PreparedRecoveryWord file (prepareExecuted file executed) metric word) :
    Ir.blocksText (runExecuted file executed earlier metric).1.body = word ∧
      ∀ item ∈ (runExecuted file executed earlier metric).1.salvage,
        RecoveryNamed (runExecuted file executed earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovered_word_exact file _ earlier metric word h,
    fun item hi => runExecuted_recovery_named file executed earlier metric item hi⟩

public theorem runRaws_recovered_word_contract (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (word : String)
    (h : PreparedRecoveryWord file (prepare file raws) metric word) :
    Ir.blocksText (runRaws file raws earlier metric).1.body = word ∧
      ∀ item ∈ (runRaws file raws earlier metric).1.salvage,
        RecoveryNamed (runRaws file raws earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovered_word_exact file _ earlier metric word h,
    fun item hi => runPreparedFinal_recovery_named file _ earlier metric item hi⟩

/-- The group belongs to the inline recovery domain of the real body plan, every withdrawal
retry included. -/
@[expose] public def PreparedRecoveryGroup (file : String) (p : Prepared) (metric : Ir.Pic.LabelMetric)
    (group : RecoveryGroup) : Prop :=
  ∀ withdrawn,
    let entry := preparedBody file p metric withdrawn
    RecoveryGroupInput entry.1.ctx entry.1.raws group

/-- Complete the braced-content interpretation from the real prepared context and state. -/
public def completeBracedRecovery (file : String) (p : Prepared) (earlier : Array Diag)
    (metric : Ir.Pic.LabelMetric) (withdrawn : Array String) (group : RecoveryGroup) :
    Ir.Doc × Array Diag × ReqSpans :=
  let (plan, initial) := preparedBody file p metric withdrawn
  let ((doc, table, report), st) :=
    (do settleDocMargins (← runBracedRecovery plan group)).run initial
  completePrepared file p earlier doc table report st

public theorem runPrepared_recovery_group_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (withdrawn : Array String)
    (group : RecoveryGroup)
    (h : RecoveryGroupInput (preparedBody file p metric withdrawn).1.ctx
      (preparedBody file p metric withdrawn).1.raws group) :
    runPrepared file p earlier metric withdrawn =
      completeBracedRecovery file p earlier metric withdrawn group := by
  rw [runPrepared_body_exact]
  unfold completeBracedRecovery
  dsimp only
  rw [runDocBody_recovery_group_exact _ group h]
  rfl

public theorem runPreparedFinal_recovery_group_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (group : RecoveryGroup)
    (h : PreparedRecoveryGroup file p metric group) :
    runPreparedFinal file p earlier metric =
      finishPreparedRuns (fun withdrawn =>
        completeBracedRecovery file p earlier metric withdrawn group) := by
  unfold runPreparedFinal
  apply congrArg finishPreparedRuns
  funext withdrawn
  exact runPrepared_recovery_group_exact file p earlier metric withdrawn group (h withdrawn)

public theorem runExecuted_recovery_group_contract (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (group : RecoveryGroup)
    (h : PreparedRecoveryGroup file (prepareExecuted file executed) metric group) :
    runExecuted file executed earlier metric =
      finishPreparedRuns (fun withdrawn => completeBracedRecovery file
        (prepareExecuted file executed) earlier metric withdrawn group) ∧
    ∀ item ∈ (runExecuted file executed earlier metric).1.salvage,
      RecoveryNamed (runExecuted file executed earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovery_group_exact file _ earlier metric group h,
    fun item hi => runExecuted_recovery_named file executed earlier metric item hi⟩

public theorem runRaws_recovery_group_contract (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (group : RecoveryGroup)
    (h : PreparedRecoveryGroup file (prepare file raws) metric group) :
    runRaws file raws earlier metric =
      finishPreparedRuns (fun withdrawn => completeBracedRecovery file
        (prepare file raws) earlier metric withdrawn group) ∧
    ∀ item ∈ (runRaws file raws earlier metric).1.salvage,
      RecoveryNamed (runRaws file raws earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovery_group_exact file _ earlier metric group h,
    fun item hi => runPreparedFinal_recovery_named file _ earlier metric item hi⟩

/-- An executed document holding a table row's control between literal neighbours, its operands
unrestricted but for those its signature reads, which no leave of its row keeps. -/
public structure ControlDocument (executed : Compat.Executed) (row : Compat.CtrlRow) where
  body : Array Raw
  pos : Pos
  docPos : Pos
  args : Array (Option (Array Raw))
  pre : List Raw
  taken : List Raw
  post : List Raw
  outsidePicture : (Compat.beginRewrite executed).outsidePicture
  document : (Compat.beginRewrite executed).raws.toList.drop
    (Compat.beginRewrite executed).index = [.env "document" body docPos]
  source : body.toList = pre ++ .ctrl row.name pos :: (taken ++ post)
  before : Compat.LiteralRaws pre
  after : Compat.LiteralRaws post
  operands : Compat.argsRead body #[] row.sig (pre.length + 1) =
    some (args, pre.length + 1 + taken.length)
  stands : (Compat.beginRewrite executed).rowStandsInBody row args

/-- The call a control document's row control stands at. -/
public def ControlDocument.call {executed : Compat.Executed} {row : Compat.CtrlRow}
    (input : ControlDocument executed row) : Compat.CtrlCall :=
  ⟨row.name, input.pos, input.args, input.body, input.pre.length + 1,
    input.pre.length + 1 + input.taken.length⟩

public theorem runExecuted_ctrlRow_contract (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (row : Compat.CtrlRow)
    (hrow : row ∈ Compat.ctrlRows) (input : ControlDocument executed row) :
    runExecuted file executed earlier metric =
      runPreparedFinal file
        (prepareRewritten file (Compat.boundaryScan file executed.raws) (macroScan executed.raws)
          executed.sourceTriggers (Compat.unusedLengths file executed.raws executed.edefReads)
          (Compat.finishCtrlRowDocument (Compat.beginRewrite executed)
            row input.call input.docPos input.pre.toArray input.post.toArray)
          executed.inputAttempts executed.mentions executed.stripped) earlier metric := by
  rw [runExecuted_rewrite_exact]
  exact ctrlRow_document_exact file _ _ _ (Compat.unusedLengths file executed.raws executed.edefReads) earlier metric
    (Compat.beginRewrite executed) input.body row input.pos input.docPos input.args
    input.pre input.taken input.post hrow input.outsidePicture
    input.document input.source input.before input.after input.operands input.stands
    executed.inputAttempts executed.mentions executed.stripped

/-- The consuming-control contract at the executed frontend: a table row's control between literal
neighbours leaves the document its emission and the state it leaves alone, unhandled controls keep
their braced content, and every recovery is named. -/
public theorem control_completion_contract (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) :
    (∀ row ∈ Compat.ctrlRows,
      ∀ input : ControlDocument executed row,
        runExecuted file executed earlier metric =
          runPreparedFinal file
            (prepareRewritten file (Compat.boundaryScan file executed.raws) (macroScan executed.raws)
              executed.sourceTriggers (Compat.unusedLengths file executed.raws executed.edefReads)
              (Compat.finishCtrlRowDocument (Compat.beginRewrite executed)
                row input.call input.docPos input.pre.toArray input.post.toArray)
              executed.inputAttempts executed.mentions executed.stripped) earlier metric) ∧
    (∀ group : RecoveryGroup,
      PreparedRecoveryGroup file (prepareExecuted file executed) metric group →
        runExecuted file executed earlier metric =
          finishPreparedRuns (fun withdrawn => completeBracedRecovery file
            (prepareExecuted file executed) earlier metric withdrawn group)) ∧
    (∀ item ∈ (runExecuted file executed earlier metric).1.salvage,
      RecoveryNamed (runExecuted file executed earlier metric).2 item) := by
  refine ⟨?_, ?_, ?_⟩
  · intro row hrow input
    exact runExecuted_ctrlRow_contract file executed earlier metric row hrow input
  · intro group hgroup
    exact (runExecuted_recovery_group_contract file executed earlier metric group hgroup).1
  · exact runExecuted_recovery_named file executed earlier metric

end LeanTex.Core.Elab
