module

public import LeanTex.Core.Elab
import all LeanTex.Core.Elab

namespace LeanTex.Core.Elab

open Parse

/-- One hole in declarative title syntax, inside a selected refused body. -/
public inductive TitleBodyContext where
  | hole
  | around (pre post : Array Raw) (inner : TitleBodyContext)
  | group (inner : TitleBodyContext) (pos : Pos)
  | env (name : String) (inner : TitleBodyContext) (pos : Pos)

@[expose] public def TitleBodyContext.fill : TitleBodyContext → Raw → Array Raw
  | .hole, raw => #[raw]
  | .around pre post inner, raw => pre ++ inner.fill raw ++ post
  | .group inner pos, raw => #[.group (inner.fill raw) pos]
  | .env name inner pos, raw => #[.env name (inner.fill raw) pos]

private theorem titleView_append (left right : Array Raw) :
    declarativeTitleList #[] (left ++ right).toList =
      declarativeTitleList #[] left.toList ++ declarativeTitleList #[] right.toList := by
  apply Array.toList_inj.mp
  simp [declarativeTitleList_toList]

private theorem TitleBodyContext.spellingView (context : TitleBodyContext)
    (aliasName internal : String) (pos : Pos)
    (hname : barCtrlName aliasName = barCtrlName internal) :
    declarativeTitleList #[] (context.fill (.ctrl aliasName pos)).toList =
      declarativeTitleList #[] (context.fill (.ctrl internal pos)).toList := by
  induction context with
  | hole => simp [TitleBodyContext.fill, declarativeTitleList, declarativeTitleRaw, hname]
  | around pre post inner ih => simp only [TitleBodyContext.fill, titleView_append, ih]
  | group inner p ih =>
    simp [TitleBodyContext.fill, declarativeTitleList, declarativeTitleRaw, ih]
  | env name inner p ih =>
    simp [TitleBodyContext.fill, declarativeTitleList, declarativeTitleRaw, ih]

public theorem refusedTitleReadout_spelling_agree (user : Array UserCmd) (bound : Nat)
    (parskip : Dim.SymGlue)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    refusedTitleReadout user bound parskip (context.fill (.ctrl row.1 pos)) =
      refusedTitleReadout user bound parskip (context.fill (.ctrl row.2 pos)) := by
  have h := List.all_eq_true.mp barCtrlName_alias_resolves row hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold refusedTitleReadout
  rw [context.spellingView row.1 row.2 pos (h.1.trans h.2.symm)]

public theorem refusedTitleAuthor_spelling_agree (user : Array UserCmd) (bound : Nat)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    refusedTitleAuthor user bound (context.fill (.ctrl row.1 pos)) =
      refusedTitleAuthor user bound (context.fill (.ctrl row.2 pos)) := by
  have h := List.all_eq_true.mp barCtrlName_alias_resolves row hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold refusedTitleAuthor
  rw [context.spellingView row.1 row.2 pos (h.1.trans h.2.symm)]

public theorem refusedTitleNotice_spelling_agree (user : Array UserCmd) (bound : Nat)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    refusedTitleNotice user bound (context.fill (.ctrl row.1 pos)) =
      refusedTitleNotice user bound (context.fill (.ctrl row.2 pos)) := by
  have h := List.all_eq_true.mp barCtrlName_alias_resolves row hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold refusedTitleNotice
  rw [context.spellingView row.1 row.2 pos (h.1.trans h.2.symm)]

public theorem titleStyleMerge_spelling_agree (s : PreState) (st : ESt)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    ((applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) }).1 =
    ((applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) }).1 := by
  rw [applyRefusedTitleStyle_result_exact, applyRefusedTitleStyle_result_exact]
  simp [titleStyleApply, refusedTitleFragment,
    refusedTitleReadout_spelling_agree s.ctx.user s.ctx.limit (Ir.texParskipOf s.page) context pos row hrow]

public theorem applyRefusedTitleStyle_spelling_agree (s : PreState) (st : ESt)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    (applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) } =
    (applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) } := by
  have h : refusedTitleFragment s (some (context.fill (.ctrl row.1 pos))) =
      refusedTitleFragment s (some (context.fill (.ctrl row.2 pos))) := by
    simp [refusedTitleFragment,
      refusedTitleReadout_spelling_agree s.ctx.user s.ctx.limit (Ir.texParskipOf s.page) context pos row hrow]
  change
    (titleStyleMerge s (refusedTitleFragment s (some (context.fill (.ctrl row.1 pos)))), _) =
    (titleStyleMerge s (refusedTitleFragment s (some (context.fill (.ctrl row.2 pos)))), _)
  simp only [h, Option.bind_some,
    refusedTitleAuthor_spelling_agree s.ctx.user s.ctx.limit context pos row hrow,
    refusedTitleNotice_spelling_agree s.ctx.user s.ctx.limit context pos row hrow]

public theorem runPreamble_spelling_agree (file : String) (p : Prepared)
    (earlier : Array Diag) (preamble : DocPreamble) (st : ESt)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    runPreamble file p earlier preamble
      { st with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) } =
    runPreamble file p earlier preamble
      { st with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) } := by
  unfold runPreamble
  rw [finishPreamble_run_congr file preamble _ _
    (applyRefusedTitleStyle_spelling_agree preamble.state st context pos row hrow)]

public theorem titleStylePhases_spelling_agree (file : String) (p : Prepared)
    (earlier : Array Diag) (phases : Array String → DocPreamble × ESt)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    finishPreparedRuns (fun withdrawn =>
      let phase := phases withdrawn
      runPreamble file p earlier phase.1
        { phase.2 with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) }) =
    finishPreparedRuns (fun withdrawn =>
      let phase := phases withdrawn
      runPreamble file p earlier phase.1
        { phase.2 with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) }) := by
  apply congrArg finishPreparedRuns
  funext withdrawn
  exact runPreamble_spelling_agree file p earlier (phases withdrawn).1 (phases withdrawn).2
    context pos row hrow

public theorem titleStyle_spelling_agree (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    finishPreparedRuns (fun withdrawn =>
      let phase := preparedPreamble file p metric withdrawn
      runPreamble file p earlier phase.1
        { phase.2 with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) }) =
    finishPreparedRuns (fun withdrawn =>
      let phase := preparedPreamble file p metric withdrawn
      runPreamble file p earlier phase.1
        { phase.2 with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) }) :=
  titleStylePhases_spelling_agree file p earlier
    (fun withdrawn => preparedPreamble file p metric withdrawn) context pos row hrow

end LeanTex.Core.Elab
