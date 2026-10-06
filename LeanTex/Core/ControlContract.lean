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

/-- A recovery is accounted by both its producer's diagnostic code and
its structured command identity. A report about a different loss at the
same command cannot discharge the kept content. -/
def RecoveryNamed (ds : Array Diag) (item : Ir.Recovered) : Prop :=
  ∃ d ∈ ds, d.kind = item.code ∧ d.subject = some item.subject

theorem accountRecoveredItem_named (ds : Array Diag) (item : Ir.Recovered)
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
    · exact ⟨_, Array.mem_push_self, rfl, rfl⟩
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

/-- Each recovery in the returned IR has its own code and command named,
even when completion resumes without the earlier ordinary log. -/
theorem accountRecovered_named (items : Array Ir.Recovered) (ds observed : Array Diag)
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

/-- The final accounting leaves a fully reported run byte-for-byte equal
before the shared tally. It cannot add a site or replace an existing span. -/
theorem accountRecovered_fixed_point (items : Array Ir.Recovered) (ds observed : Array Diag)
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

/-- The actual document completion names the recovery census of the
document it returns, after colour realization and all document judges. -/
theorem completePrepared_recovery_named (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) (item : Ir.Recovered)
    (h : item ∈ (completePrepared file p earlier doc table report st).1.salvage) :
    RecoveryNamed (completePrepared file p earlier doc table report st).2.1 item := by
  unfold completePrepared at h ⊢
  dsimp only at h ⊢
  exact recovery_tally _ item (accountRecovered_named _ _ _ item h)

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
    ⟨d, hd, _, hs⟩
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

/-- The final document judges can realize colours but conserve the body's
text census. This is the document returned by the production completion. -/
theorem completePrepared_body_text (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) :
    Ir.blocksText (completePrepared file p earlier doc table report st).1.body =
      Ir.blocksText doc.body := by
  change Ir.blocksText (Contrast.realizeDoc doc (colorSiteOf st.spans.colors)).1.body = _
  unfold Contrast.realizeDoc
  dsimp only
  split
  · rfl
  · exact Ir.recolorRoles_text _ _ _ doc.body

/-- The input condition is checked on the context and body produced by
the real declaration/class preparation, for each withdrawal environment.
It assumes neither an elaborated paragraph nor a final text census. -/
def PreparedRecoveryWord (file : String) (p : Prepared) (metric : Ir.Pic.LabelMetric)
    (word : String) : Prop :=
  ∀ withdrawn,
    let entry := preparedBody file p metric withdrawn
    RecoveryWordInput entry.1.ctx entry.1.raws word

/-- Unknown-command content reaches the returned document through the
actual prepared frontend: class preparation, the recursive body interpreter,
numbering, reference resolution and every final document judge. -/
theorem runPrepared_recovered_word_exact (file : String) (p : Prepared)
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
    simp only [hx] at hb ⊢
    rw [completePrepared_body_text]
    exact hb

/-- Withdrawal chooses one complete production run. Source erasure then
preserves its census, so the final file-free document contains the word. -/
theorem runPreparedFinal_recovered_word_exact (file : String) (p : Prepared)
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

/-- The corrected unknown-control half of the control contract: the
actual final document retains its literal argument, and every recovery in
that document is named by its own code and subject in the final log.
Together with the consuming-control continuation equations above,
this distinguishes consumed controls from content recovery. -/
theorem runExecuted_recovered_word_contract (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (word : String)
    (h : PreparedRecoveryWord file (prepareExecuted file executed) metric word) :
    Ir.blocksText (runExecuted file executed earlier metric).1.body = word ∧
      ∀ item ∈ (runExecuted file executed earlier metric).1.salvage,
        RecoveryNamed (runExecuted file executed earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovered_word_exact file _ earlier metric word h,
    fun item hi => runExecuted_recovery_named file executed earlier metric item hi⟩

/-- The parsed, file-free entrypoint has the same complete contract. -/
theorem runRaws_recovered_word_contract (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (word : String)
    (h : PreparedRecoveryWord file (prepare file raws) metric word) :
    Ir.blocksText (runRaws file raws earlier metric).1.body = word ∧
      ∀ item ∈ (runRaws file raws earlier metric).1.salvage,
        RecoveryNamed (runRaws file raws earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovered_word_exact file _ earlier metric word h,
    fun item hi => runPreparedFinal_recovery_named file _ earlier metric item hi⟩

/-- The group belongs to the inline recovery domain in the real body plan,
including every withdrawal retry. Neither body output nor diagnostic
membership is a premise. -/
def PreparedRecoveryGroup (file : String) (p : Prepared) (metric : Ir.Pic.LabelMetric)
    (group : RecoveryGroup) : Prop :=
  ∀ withdrawn,
    let entry := preparedBody file p metric withdrawn
    RecoveryGroupInput entry.1.ctx entry.1.raws group

/-- Complete the braced-content interpretation from the real prepared
context and state. This shares production's document continuation and final
judges; only the already-proved body equation changes its input. -/
def completeBracedRecovery (file : String) (p : Prepared) (earlier : Array Diag)
    (metric : Ir.Pic.LabelMetric) (withdrawn : Array String) (group : RecoveryGroup) :
    Ir.Doc × Array Diag × ReqSpans :=
  let (plan, initial) := preparedBody file p metric withdrawn
  let ((doc, table, report), st) := (runBracedRecovery plan group).run initial
  completePrepared file p earlier doc table report st

/-- The actual prepared frontend agrees with ordinary braced interpretation
of arbitrary inline group content, with the original control's warning and
recovery attribution. All final document judges see that same result. -/
theorem runPrepared_recovery_group_exact (file : String) (p : Prepared)
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

/-- Withdrawal and source erasure preserve the complete braced-content
equation. In particular both the returned IR and final diagnostic sequence
are fixed by that interpretation. -/
theorem runPreparedFinal_recovery_group_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (group : RecoveryGroup)
    (h : PreparedRecoveryGroup file p metric group) :
    runPreparedFinal file p earlier metric =
      finishPreparedRuns (fun withdrawn =>
        completeBracedRecovery file p earlier metric withdrawn group) := by
  unfold runPreparedFinal
  apply congrArg finishPreparedRuns
  funext withdrawn
  exact runPrepared_recovery_group_exact file p earlier metric withdrawn group (h withdrawn)

/-- The fulfilled-input entrypoint's whole recovery contract. An unhandled
control keeps the interpretation of its arbitrary inline group, and every
recovered item in the final document is named by its producer's code and
subject. The consuming-control equations earlier in this module give the
other half: registered control operands never reach that interpreter. -/
theorem runExecuted_recovery_group_contract (file : String) (executed : Compat.Executed)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (group : RecoveryGroup)
    (h : PreparedRecoveryGroup file (prepareExecuted file executed) metric group) :
    runExecuted file executed earlier metric =
      finishPreparedRuns (fun withdrawn => completeBracedRecovery file
        (prepareExecuted file executed) earlier metric withdrawn group) ∧
    ∀ item ∈ (runExecuted file executed earlier metric).1.salvage,
      RecoveryNamed (runExecuted file executed earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovery_group_exact file _ earlier metric group h,
    fun item hi => runExecuted_recovery_named file executed earlier metric item hi⟩

/-- The parsed file-free entrypoint carries the identical complete contract,
after actual compatibility execution and declaration/class preparation. -/
theorem runRaws_recovery_group_contract (file : String) (raws : Array Raw)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (group : RecoveryGroup)
    (h : PreparedRecoveryGroup file (prepare file raws) metric group) :
    runRaws file raws earlier metric =
      finishPreparedRuns (fun withdrawn => completeBracedRecovery file
        (prepare file raws) earlier metric withdrawn group) ∧
    ∀ item ∈ (runRaws file raws earlier metric).1.salvage,
      RecoveryNamed (runRaws file raws earlier metric).2 item := by
  exact ⟨runPreparedFinal_recovery_group_exact file _ earlier metric group h,
    fun item hi => runPreparedFinal_recovery_named file _ earlier metric item hi⟩

end LeanTex.Core.Elab
