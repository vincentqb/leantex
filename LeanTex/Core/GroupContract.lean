module

public import LeanTex.Core.Elab

import all LeanTex.Core.Elab

/-!
# A group the block walk meets restores its declaration state

`texGroup_scope_id` is the restore as an equation over any action. The
statements here read it through the block walk's own dispatch for two
shapes: a document whose body is one environment holding block content, and
one whose body is one braced group of block content with no paragraph end.
Both go through `texGroup`, so the state after them is the state before
them (TeXbook ch. 24), the global assignments logged inside aside. The rest
of the walk's dispatch — a group split at a paragraph end, a column, an
inline group, a group among other raws — goes through the same `texGroup` or
`inlineGroup` with no theorem of its own here; `Tests.GroupScope` holds
probes of those against lualatex.
-/

namespace LeanTex.Core.Elab

open Parse Ir

/-- The spine past its last raw with nothing open: whatever the flow
generation, it returns its blocks and leaves the state alone. -/
private theorem elabBlocksGo_past (ctx : Ctx) (st : ESt) (raws : Array Raw) (i : Nat)
    (blocks : Array Block) (gen : Nat)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hi : raws.size ≤ i) :
    (elabBlocksGo ctx raws i blocks #[] gen).run st = (blocks, st) := by
  have hf : (flowCtx ctx st gen).macroRoles = ({file := ""} : Ctx).macroRoles := by
    unfold flowCtx
    split <;> exact hm
  rw [elabBlocksGo, run_get]
  simp only [show ¬ i < raws.size from Nat.not_lt.mpr hi, ↓reduceDIte]
  simp [blockMacroStep, flowMCtx, hf, blockMacroKinds, hi, flushPara, carryDecls_empty,
    closeBlockFrameSources, commonOrigins, moveMacroRuns, closeMacroRuns, MacroRoles.empty]
  rfl

private theorem pictureInSentence_alone (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos) :
    pictureInSentence ctx n #[] #[.env n body pos] 0 pos = pure () := by
  simp [pictureInSentence]

/-- The spine at an environment standing alone, nothing open before it:
the environment's arm through `envGroup`, then the walk past it. -/
private theorem elabBlocksGo_env_alone (ctx : Ctx) (st : ESt) (n : String) (body : Array Raw)
    (pos : Pos) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hb : bodyIsBlock body = true) (hl : n ≠ Compat.linkedBoxRowMark) :
    (elabBlocksGo ctx #[.env n body pos] 0 #[] #[] st.flowGen).run st =
      ((do
        let bs ← envGroup n ctx.palette false false false 0 (elabEnvArm ctx n body pos #[])
        elabBlocksGo ctx #[.env n body pos] 1 bs #[] st.flowGen) : EM (Array Block)).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 0 #[] #[] hm (by simp) (by simpa [Raw.origins?] using hp)]
  simp [hl, hb, pictureInSentence_alone, flushPara_empty ctx _ hm, Ir.flushedText_empty_exact,
    Ir.lastLeavesEndPe_empty_exact, endPeAt, parFollows]

/-- The spine at a braced group of block content standing alone, nothing
open before it: the group through `groupBlocks`, then the walk past it. -/
private theorem elabBlocksGo_group_alone (ctx : Ctx) (st : ESt) (body : Array Raw)
    (pos : Pos) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hpar : body.any isParRaw = false) (hb : bodyIsBlock body = true) :
    (elabBlocksGo ctx #[.group body pos] 0 #[] #[] st.flowGen).run st =
      ((do
        let inner ← groupBlocks ctx.palette
          (splicedFrameScope (some 0) (elabBlockScope ctx body))
        elabBlocksGo ctx #[.group body pos] 1 (#[] ++ inner) #[] st.flowGen) :
        EM (Array Block)).run st := by
  have ha : isArgument #[] = false := by
    rw [isArgument]
    simp [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 0 #[] #[] hm (by simp) (by simpa [Raw.origins?] using hp)]
  simp [hpar, hb, ha, flushPara_empty ctx _ hm]

/-- What the walk's tail does to the state: nothing the declaration state
reads. -/
private theorem closeBlockScope_scope (ctx : Ctx) (base : Option Nat) (bs : Array Block)
    (st : ESt) : ((closeBlockScope ctx #[] base bs).run st).2.scope = st.scope := by
  simp [closeBlockScope, closeLengthScope, setFrameSourceBase]
  rfl

/-- `texGroup`'s blocks with its epoch appended keep its state. -/
private theorem groupBlocks_state (base : Palette) (act : EM (Array Block)) (st : ESt) :
    ((groupBlocks base act).run st).2 = ((texGroup base act).run st).2 := by
  rfl

private theorem envGroup_state (n : String) (base : Palette) (inPar parEnd afterEnv : Bool)
    (k : Nat) (act : EM (Array Block)) (st : ESt) (hfile : Parse.inputEnvFile? n = none) :
    ((envGroup n base inPar parEnd afterEnv k act).run st).2 =
      ((texGroup base act).run st).2 := by
  simp [envGroup, hfile]
  rfl

/-- **An environment is a group**: a body that is one environment holding
block content (`bodyIsBlock`) leaves the declaration state as its `\begin`
found it when nothing inside made a global assignment, whatever the
environment's arm does — `texGroup_scope_id` read through the walk's own
dispatch. An `\input` file's wrapper names a file and opens no group, so it
is not one. -/
public theorem elabBlocks_env_scope_id (ctx : Ctx) (st : ESt) (n : String) (body : Array Raw)
    (pos : Pos) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hb : bodyIsBlock body = true) (hl : n ≠ Compat.linkedBoxRowMark)
    (hfile : Parse.inputEnvFile? n = none)
    (hglobal : ((elabBlocks ctx #[.env n body pos]).run st).2.scope.globals = st.scope.globals) :
    ((elabBlocks ctx #[.env n body pos]).run st).2.scope = st.scope := by
  have hlen : openLengthScope ctx #[.env n body pos] =
      (#[], ⟨#[.env n body pos], Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩) := by
    rw [openLengthScope, lengthScopeKeys?]
    rfl
  have hrun := elabBlocks_scope ctx st #[.env n body pos] hm hlen
  have hgo := elabBlocksGo_env_alone ctx (enterBodyScope st) n body pos hm hp hb hl
  rw [show (enterBodyScope st).flowGen = st.flowGen from rfl] at hgo
  let act := elabEnvArm ctx n body pos #[]
  let s1 := (envGroup n ctx.palette false false false 0 act).run (enterBodyScope st)
  have hpast := elabBlocksGo_past ctx s1.2 #[.env n body pos] 1 s1.1 st.flowGen hm (by simp)
  have hstate : s1.2 = ((texGroup ctx.palette act).run (enterBodyScope st)).2 :=
    envGroup_state n ctx.palette false false false 0 act (enterBodyScope st) hfile
  have h0 : (elabBlocksGo ctx #[.env n body pos] 0 #[] #[] st.flowGen).run (enterBodyScope st) =
      (s1.1, s1.2) := by
    rw [hgo]
    exact hpast
  have hfinal : (elabBlocks ctx #[.env n body pos]).run st =
      (closeBlockScope ctx #[] st.spans.frames.base s1.1).run s1.2 := by
    rw [hrun]
    show (closeBlockScope ctx #[] st.spans.frames.base
        ((elabBlocksGo ctx #[.env n body pos] 0 #[] #[] st.flowGen).run (enterBodyScope st)).1).run
        ((elabBlocksGo ctx #[.env n body pos] 0 #[] #[] st.flowGen).run (enterBodyScope st)).2 = _
    rw [h0]
  have hclose := closeBlockScope_scope ctx st.spans.frames.base s1.1 s1.2
  rw [hfinal, hclose, hstate]
  rw [hfinal, hclose, hstate, texGroup_globals_exact] at hglobal
  exact texGroup_scope_id ctx.palette act (enterBodyScope st) hglobal

/-- **A braced group of block content is a group**: a body that is one such
group with no paragraph end inside leaves the declaration state as its `{`
found it when nothing inside made a global assignment. -/
public theorem elabBlocks_group_scope_id (ctx : Ctx) (st : ESt) (body : Array Raw)
    (pos : Pos) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hpar : body.any isParRaw = false) (hb : bodyIsBlock body = true)
    (hglobal : ((elabBlocks ctx #[.group body pos]).run st).2.scope.globals = st.scope.globals) :
    ((elabBlocks ctx #[.group body pos]).run st).2.scope = st.scope := by
  have hlen : openLengthScope ctx #[.group body pos] =
      (#[], ⟨#[.group body pos], Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩) := by
    rw [openLengthScope, lengthScopeKeys?]
    rfl
  have hrun := elabBlocks_scope ctx st #[.group body pos] hm hlen
  have hgo := elabBlocksGo_group_alone ctx (enterBodyScope st) body pos hm hp hpar hb
  rw [show (enterBodyScope st).flowGen = st.flowGen from rfl] at hgo
  let act := splicedFrameScope (some 0) (elabBlockScope ctx body)
  let s1 := (groupBlocks ctx.palette act).run (enterBodyScope st)
  have hpast := elabBlocksGo_past ctx s1.2 #[.group body pos] 1 (#[] ++ s1.1) st.flowGen hm
    (by simp)
  have hstate : s1.2 = ((texGroup ctx.palette act).run (enterBodyScope st)).2 :=
    groupBlocks_state ctx.palette act (enterBodyScope st)
  have h0 : (elabBlocksGo ctx #[.group body pos] 0 #[] #[] st.flowGen).run (enterBodyScope st) =
      (#[] ++ s1.1, s1.2) := by
    rw [hgo]
    exact hpast
  have hfinal : (elabBlocks ctx #[.group body pos]).run st =
      (closeBlockScope ctx #[] st.spans.frames.base (#[] ++ s1.1)).run s1.2 := by
    rw [hrun]
    show (closeBlockScope ctx #[] st.spans.frames.base
        ((elabBlocksGo ctx #[.group body pos] 0 #[] #[] st.flowGen).run (enterBodyScope st)).1).run
        ((elabBlocksGo ctx #[.group body pos] 0 #[] #[] st.flowGen).run (enterBodyScope st)).2 = _
    rw [h0]
  have hclose := closeBlockScope_scope ctx st.spans.frames.base (#[] ++ s1.1) s1.2
  rw [hfinal, hclose, hstate]
  rw [hfinal, hclose, hstate, texGroup_globals_exact] at hglobal
  exact texGroup_scope_id ctx.palette act (enterBodyScope st) hglobal

end LeanTex.Core.Elab
