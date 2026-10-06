import LeanTex.Core.Elab

namespace LeanTex.Core.Elab

open Parse

/-- One hole in declarative title syntax. Prefixes, suffixes, nested groups,
and environments are arbitrary. This is deliberately a context inside a
selected refused body, not an executable preamble context. -/
inductive TitleBodyContext where
  | hole
  | around (pre post : Array Raw) (inner : TitleBodyContext)
  | group (inner : TitleBodyContext) (pos : Pos)
  | env (name : String) (inner : TitleBodyContext) (pos : Pos)

def TitleBodyContext.fill : TitleBodyContext → Raw → Array Raw
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
theorem refusedTitleReadout_spelling_agree (user : Array UserCmd) (bound : Nat)
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
theorem titleStyle_spelling_agree (s : PreState) (st : ESt)
    (context : TitleBodyContext) (pos : Pos) (row : String × String)
    (hrow : row ∈ beamerInsertAlias) :
    ((applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) }).1 =
    ((applyRefusedTitleStyle s).run
      { st with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) }).1 := by
  rw [applyRefusedTitleStyle_result_exact, applyRefusedTitleStyle_result_exact]
  simp [titleStyleApply, refusedTitleFragment,
    refusedTitleReadout_spelling_agree s.ctx.user s.ctx.limit context pos row hrow]

end LeanTex.Core.Elab
