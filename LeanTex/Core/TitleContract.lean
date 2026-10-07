module

public import LeanTex.Core.Elab
import all LeanTex.Core.Elab

namespace LeanTex.Core.Elab

open Parse

/-- One hole in declarative title syntax. Prefixes, suffixes, nested groups,
and environments are arbitrary. This is deliberately a context inside a
selected refused body, not an executable preamble context. -/
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

/-- Every alias at every declarative occurrence preserves the complete
interpreted style fragment. The conclusion includes rule weights, author
furniture, font, spacing, and alignment, not merely the scanner's events. -/
public theorem refusedTitleReadout_spelling_agree (user : Array UserCmd) (bound : Nat)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    refusedTitleReadout user bound (context.fill (.ctrl row.1 pos)) =
      refusedTitleReadout user bound (context.fill (.ctrl row.2 pos)) := by
  have h := List.all_eq_true.mp barCtrlName_alias_resolves row hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold refusedTitleReadout
  rw [context.spellingView row.1 row.2 pos (h.1.trans h.2.symm)]

/-- The production preamble finalizer, for any completed preamble state and
any alias occurrence inside its selected refused body, returns the same
entire `PreState`. In particular the document's `titlepage` entry is equal
after `Theme.styleMerge` and `Styles.declare`, with explicit declarations
retaining their precedence. This replaces global source-spelling equality:
execution may legitimately inspect a control word's spelling. -/
public theorem titleStyleMerge_spelling_agree (s : PreState) (st : ESt)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    ((applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) }).1 =
    ((applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) }).1 := by
  rw [applyRefusedTitleStyle_result_exact, applyRefusedTitleStyle_result_exact]
  simp [titleStyleApply, refusedTitleFragment,
    refusedTitleReadout_spelling_agree s.ctx.user s.ctx.limit context pos row hrow]

/-- Reading the selected body retires its syntax in every branch, including
an empty readout or a user definition taking precedence. The entire state,
with the original refusal's provenance, agrees after this operation. -/
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
      refusedTitleReadout_spelling_agree s.ctx.user s.ctx.limit context pos row hrow]
  change
    (titleStyleMerge s (refusedTitleFragment s (some (context.fill (.ctrl row.1 pos)))), _) =
    (titleStyleMerge s (refusedTitleFragment s (some (context.fill (.ctrl row.2 pos)))), _)
  simp only [h]

/-- The complete production prepared pass agrees, including its body,
styles, diagnostics, picture requests and request spans. No assumption on
the continuation's class, declarations, body or diagnostics is needed. -/
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

/-- Alias equivalence through the complete frontend after source execution
has selected a refused title body. The phase family permits arbitrary
class/declaration/body state on each withdrawal pass. Each side replaces
one declarative occurrence in that selected body, then uses the production
body interpreter, all document judges, boundary withdrawal, location
erasure and final reference diagnostics.

The equality is of the whole returned document and diagnostic array, so
both backend artifacts agree for any fixed font environment. It does not
normalize executable source: `elabTitleBoundaryChecks` retains the
conditional that distinguishes the original spellings. -/
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

/-- The same contract using the actual production declaration folds on
both passes. Its boundary is a selected declarative body: source execution
has already decided which body and bindings are in force. Only the chosen
occurrence changes; every other field comes from `preparedPreamble`.
`runPreparedFinal_preamble_exact` identifies this completion with the one
used by `runRaws` and `runExecuted`. -/
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
