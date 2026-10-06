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

end LeanTex.Core.Elab
