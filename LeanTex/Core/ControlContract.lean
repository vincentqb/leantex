import LeanTex.Core.Elab

namespace LeanTex.Core.Elab

open Parse

/-- Completion of an actual compatibility checkpoint by the production
text rewrite, declaration/body interpreter, document judges, boundary
withdrawal and reference diagnostics. The earlier picture/macro scans and
source attribution are held at their actual preparation boundary. -/
def runRewriteFinal (file : String) (picScan : Compat.BoundaryScan)
    (picMacros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) : Ir.Doc × Array Diag :=
  runPreparedFinal file
    (prepareRewritten file picScan picMacros triggers priorDiags (Compat.finishRewrite cursor))
    earlier metric

/-- The input-fulfilling frontend calls this exact completion with its real
executed state and real scan metadata. No second interpreter is introduced
for the contract. -/
theorem runExecuted_rewrite_exact (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) :
    runExecuted file executed earlier metric =
      runRewriteFinal file (Compat.boundaryScan executed.raws) (macroScan executed.raws)
        executed.sourceTriggers #[] earlier metric (Compat.beginRewrite executed) := rfl

/-- A consuming control's complete returned document and diagnostics are
computed from the retained body and its registered report. Consumed groups
never enter text rewriting, body elaboration, the withdrawal retry or any
final judge. The syntax premises describe the actual unread document, not
an assumed equality of outputs. -/
theorem meaningFree_document_exact (file : String) (scan : Compat.BoundaryScan)
    (macros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) (body : Array Raw)
    (name : String) (arity : Nat) (note : Option String) (pos docPos : Pos)
    (pre taken post : List Raw) (args : List (Array Raw))
    (hm : (name, arity, note) ∈ Compat.meaningFree)
    (hp : cursor.outsidePicture) (hl : cursor.outsideList)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body docPos])
    (hb : body.toList = pre ++ .ctrl name pos :: (taken ++ post))
    (hpre : Compat.LiteralRaws pre) (hpost : Compat.LiteralRaws post)
    (hn : args.length = arity)
    (hg : Compat.GroupPrefix body (pre.length + 1) args (pre.length + 1 + taken.length)) :
    runRewriteFinal file scan macros triggers priorDiags earlier metric cursor =
      runPreparedFinal file
        (prepareRewritten file scan macros triggers priorDiags
          (Compat.finishMeaningFreeDocument cursor name note pos docPos
            (pre.toArray ++ post.toArray))) earlier metric := by
  unfold runRewriteFinal
  rw [Compat.finishRewrite_meaningFree_document_exact cursor body name arity note pos docPos
    pre taken post args hm hp hl hs hb hpre hpost hn hg]

theorem configSkip_document_exact (file : String) (scan : Compat.BoundaryScan)
    (macros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) (body : Array Raw)
    (name : String) (arity : Nat) (msg : String) (help : Option String) (pos docPos : Pos)
    (pre taken post : List Raw) (args : List (Array Raw))
    (hm : (name, arity, msg, help) ∈ Compat.configSkip)
    (hp : cursor.outsidePicture) (hl : cursor.outsideList)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body docPos])
    (hb : body.toList = pre ++ .ctrl name pos :: (taken ++ post))
    (hpre : Compat.LiteralRaws pre) (hpost : Compat.LiteralRaws post)
    (hn : args.length = arity)
    (hg : Compat.GroupPrefix body (pre.length + 1) args (pre.length + 1 + taken.length)) :
    runRewriteFinal file scan macros triggers priorDiags earlier metric cursor =
      runPreparedFinal file
        (prepareRewritten file scan macros triggers priorDiags
          (Compat.finishConfigSkipDocument cursor name msg help pos docPos
            (pre.toArray ++ post.toArray))) earlier metric := by
  unfold runRewriteFinal
  rw [Compat.finishRewrite_configSkip_document_exact cursor body name arity msg help pos docPos
    pre taken post args hm hp hl hs hb hpre hpost hn hg]

/-- Arbitrary replacement of every consumed group leaves the entire final
document and diagnostic array equal. Earlier execution and metadata are
fixed; each side then runs the actual compatibility and Elab continuations.
This is stronger than absence of one chosen keyword and does not depend on
how either backend paints the common returned IR. -/
theorem meaningFree_operands_agree (file : String) (scan : Compat.BoundaryScan)
    (macros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) (left right : Array Raw)
    (name : String) (arity : Nat) (note : Option String) (pos docPos : Pos)
    (pre post takenLeft takenRight : List Raw) (argsLeft argsRight : List (Array Raw))
    (hm : (name, arity, note) ∈ Compat.meaningFree)
    (hp : cursor.outsidePicture) (hl : cursor.outsideList)
    (hleft : left.toList = pre ++ .ctrl name pos :: (takenLeft ++ post))
    (hright : right.toList = pre ++ .ctrl name pos :: (takenRight ++ post))
    (hpre : Compat.LiteralRaws pre) (hpost : Compat.LiteralRaws post)
    (hnleft : argsLeft.length = arity) (hnright : argsRight.length = arity)
    (hgleft : Compat.GroupPrefix left (pre.length + 1) argsLeft
      (pre.length + 1 + takenLeft.length))
    (hgright : Compat.GroupPrefix right (pre.length + 1) argsRight
      (pre.length + 1 + takenRight.length)) :
    runRewriteFinal file scan macros triggers priorDiags earlier metric
      (cursor.withDocument left docPos) =
    runRewriteFinal file scan macros triggers priorDiags earlier metric
      (cursor.withDocument right docPos) := by
  rw [meaningFree_document_exact file scan macros triggers priorDiags earlier metric
    (cursor.withDocument left docPos) left name arity note pos docPos pre takenLeft post
    argsLeft hm hp hl rfl hleft hpre hpost hnleft hgleft,
    meaningFree_document_exact file scan macros triggers priorDiags earlier metric
    (cursor.withDocument right docPos) right name arity note pos docPos pre takenRight post
    argsRight hm hp hl rfl hright hpre hpost hnright hgright,
    Compat.finishMeaningFreeDocument_source_exact,
    Compat.finishMeaningFreeDocument_source_exact]

theorem configSkip_operands_agree (file : String) (scan : Compat.BoundaryScan)
    (macros : Array (String × String)) (triggers : Compat.SourceTriggers)
    (priorDiags earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (cursor : Compat.RewriteCursor) (left right : Array Raw)
    (name : String) (arity : Nat) (msg : String) (help : Option String) (pos docPos : Pos)
    (pre post takenLeft takenRight : List Raw) (argsLeft argsRight : List (Array Raw))
    (hm : (name, arity, msg, help) ∈ Compat.configSkip)
    (hp : cursor.outsidePicture) (hl : cursor.outsideList)
    (hleft : left.toList = pre ++ .ctrl name pos :: (takenLeft ++ post))
    (hright : right.toList = pre ++ .ctrl name pos :: (takenRight ++ post))
    (hpre : Compat.LiteralRaws pre) (hpost : Compat.LiteralRaws post)
    (hnleft : argsLeft.length = arity) (hnright : argsRight.length = arity)
    (hgleft : Compat.GroupPrefix left (pre.length + 1) argsLeft
      (pre.length + 1 + takenLeft.length))
    (hgright : Compat.GroupPrefix right (pre.length + 1) argsRight
      (pre.length + 1 + takenRight.length)) :
    runRewriteFinal file scan macros triggers priorDiags earlier metric
      (cursor.withDocument left docPos) =
    runRewriteFinal file scan macros triggers priorDiags earlier metric
      (cursor.withDocument right docPos) := by
  rw [configSkip_document_exact file scan macros triggers priorDiags earlier metric
    (cursor.withDocument left docPos) left name arity msg help pos docPos pre takenLeft post
    argsLeft hm hp hl rfl hleft hpre hpost hnleft hgleft,
    configSkip_document_exact file scan macros triggers priorDiags earlier metric
    (cursor.withDocument right docPos) right name arity msg help pos docPos pre takenRight post
    argsRight hm hp hl rfl hright hpre hpost hnright hgright,
    Compat.finishConfigSkipDocument_source_exact,
    Compat.finishConfigSkipDocument_source_exact]

/-- Recovery is accounted by its structured command identity, the same
census key the final diagnostic judge reads. -/
def RecoveryNamed (ds : Array Diag) (item : Ir.Recovered) : Prop :=
  ∃ d ∈ ds, d.subject = some item.subject

theorem accountRecoveredItem_named (ds : Array Diag) (item : Ir.Recovered) :
    RecoveryNamed (accountRecoveredItem ds item) item := by
  unfold accountRecoveredItem
  split
  · rename_i h
    rcases Array.any_eq_true'.mp h with ⟨d, hd, hs⟩
    exact ⟨d, hd, by simpa only [beq_iff_eq] using hs⟩
  · exact ⟨recoveryDiagnostic item, Array.mem_push_self,
      recoveryDiagnostic_subject_exact item⟩

private theorem recoveryFold_preserves (items : List Ir.Recovered)
    (ds : Array Diag) (item : Ir.Recovered) (h : RecoveryNamed ds item) :
    RecoveryNamed (items.foldl accountRecoveredItem ds) item := by
  induction items generalizing ds with
  | nil => exact h
  | cons x xs ih =>
    rcases h with ⟨d, hd, hs⟩
    exact ih _ ⟨d, accountRecoveredItem_mem ds x d hd, hs⟩

private theorem recoveryFold_names (items : List Ir.Recovered)
    (ds : Array Diag) (item : Ir.Recovered) (h : item ∈ items) :
    RecoveryNamed (items.foldl accountRecoveredItem ds) item := by
  induction items generalizing ds with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact recoveryFold_preserves xs _ item (accountRecoveredItem_named ds item)
    · exact ih _ h

/-- Each recovery in the returned IR has a report, even when completion
resumes a document whose earlier log did not accompany its recovery data. -/
theorem accountRecovered_named (items : Array Ir.Recovered)
    (ds : Array Diag) (item : Ir.Recovered) (h : item ∈ items) :
    RecoveryNamed (accountRecovered items ds) item := by
  rw [accountRecovered_run_exact, ← Array.foldl_toList]
  exact recoveryFold_names items.toList ds item (Array.mem_toList_iff.mpr h)

private theorem recovery_tally (ds : Array Diag) (item : Ir.Recovered)
    (h : RecoveryNamed ds item) : RecoveryNamed (Diag.tallySites ds) item := by
  rcases h with ⟨d, hd, hs⟩
  rcases Array.mem_iff_getElem.mp hd with ⟨i, hi, he⟩
  rcases Diag.tallySites_id ds i hi with ⟨d', hd', _, _, _, _, _, hs'⟩
  exact ⟨d', Array.mem_iff_getElem?.mpr ⟨i, hd'⟩, hs'.trans (he ▸ hs)⟩

/-- The actual document completion names the recovery census of the
document it returns, after colour realization and all document judges. -/
theorem completePrepared_recovery_named (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) (item : Ir.Recovered)
    (h : item ∈ (completePrepared file p earlier doc table report st).1.salvage) :
    RecoveryNamed (completePrepared file p earlier doc table report st).2.1 item := by
  unfold completePrepared at h ⊢
  dsimp only at h ⊢
  exact recovery_tally _ item (accountRecovered_named _ _ item h)

/-- Every production declaration/body run reaches the accounting boundary.
No premise about the body's commands or its earlier diagnostic log is
needed. -/
theorem runPrepared_recovery_named (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (withdrawn : Array String)
    (item : Ir.Recovered)
    (h : item ∈ (runPrepared file p earlier metric withdrawn).1.salvage) :
    RecoveryNamed (runPrepared file p earlier metric withdrawn).2.1 item := by
  rcases runPrepared_complete_exact file p earlier metric withdrawn with
    ⟨doc, table, report, st, heq⟩
  rw [heq] at h ⊢
  exact completePrepared_recovery_named file p earlier doc table report st item h

attribute [local irreducible] runPrepared prepare prepareExecuted

/-- Withdrawal selects a complete run; source erasure and reference
diagnostics preserve its recovery identities. This is the final public
frontend result, not the local warning helper's log. -/
theorem runPreparedFinal_recovery_named (file : String) (p : Prepared)
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

/-- Every recovery record in the file-free frontend's returned document is
named in its final diagnostic array, for arbitrary parsed input. -/
theorem runRaws_recovery_named (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (item : Ir.Recovered)
    (h : item ∈ (runRaws file raws earlier metric).1.salvage) :
    (runRaws file raws earlier metric).2.any (·.subject == some item.subject) = true := by
  rcases runPreparedFinal_recovery_named file (prepare file raws) earlier metric item h with
    ⟨d, hd, hs⟩
  exact Array.any_eq_true'.mpr ⟨d, hd, by simp only [hs, BEq.rfl]⟩

/-- The fulfilled-input frontend returns the same recovery guarantee. -/
theorem runExecuted_recovery_named (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (item : Ir.Recovered)
    (h : item ∈ (runExecuted file executed earlier metric).1.salvage) :
    RecoveryNamed (runExecuted file executed earlier metric).2 item :=
  runPreparedFinal_recovery_named file (prepareExecuted file executed) earlier metric item h

/-- Lexing and parsing feed the same production frontend; its final
recovery census is named for every source string, including malformed ones. -/
theorem run_recovery_named (file input : String) (item : Ir.Recovered)
    (h : item ∈ (run file input).1.salvage) :
    (run file input).2.any (·.subject == some item.subject) = true :=
  runRaws_recovery_named file _ _ _ item h

end LeanTex.Core.Elab
