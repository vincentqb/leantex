module

public import LeanTex.Core.TextAccount
public import LeanTex.Core.Elab
public import LeanTex.Core.TextSymData

import all LeanTex.Core.Ir
import all LeanTex.Core.Elab
import all LeanTex.Core.Parse
import all LeanTex.Core.Diag

namespace LeanTex.Core.Text

/-- Smart punctuation keeps the spelling and the white space it reads, after what it has set. -/
theorem smartPunct_go_canon (l prev : List Char) :
    ∃ x, Ir.smartPunct.go l prev = prev.reverse ++ x ∧ canon x = canon l ∧
      x.filter (·.isWhitespace) = l.filter (·.isWhitespace) := by
  fun_induction Ir.smartPunct.go l prev with
  | case1 prev => exact ⟨[], by simp, by simp, by simp⟩
  | _ =>
    rename_i ih
    obtain ⟨x, hx, hs, hw⟩ := ih
    refine ⟨_ :: x, by rw [hx, List.reverse_cons, List.append_assoc]; rfl, ?_, ?_⟩
    · simp only [canon, List.flatMap_cons] at hs ⊢
      rw [hs]
      all_goals first
        | (split <;> simp [spell])
        | simp [spell]
    · simp only [List.filter_cons, hw]
      all_goals split <;> simp_all [Char.isWhitespace]

theorem smartPunct_canon (s : String) :
    canon (Ir.smartPunct s).toList = canon s.toList ∧
      (Ir.smartPunct s).toList.filter (·.isWhitespace) = s.toList.filter (·.isWhitespace) := by
  obtain ⟨x, hx, hs, hw⟩ := smartPunct_go_canon s.toList []
  simp [Ir.smartPunct, hx, hs, hw]

theorem smartPunctAfter_canon (lead : Option Char) (s : String) :
    canon (Ir.smartPunctAfter lead s).toList = canon s.toList ∧
      (Ir.smartPunctAfter lead s).toList.filter (·.isWhitespace) =
        s.toList.filter (·.isWhitespace) := by
  cases lead with
  | none => exact smartPunct_canon s
  | some c =>
    obtain ⟨x, hx, hs, hw⟩ := smartPunct_go_canon s.toList [c]
    simp [Ir.smartPunctAfter, hx, hs, hw]

/-- Smart punctuation reads alike from either origin. -/
theorem chars_smart (named : List Span) (o : Origin) (s : String) :
    canon (keep named (chars o (Ir.smartPunct s))) = canon (keep named (chars o s)) := by
  cases o with
  | source sp =>
    simp only [keep_source]
    split
    · rfl
    · exact (smartPunct_canon s).1
  | engine =>
    rw [keep_engine, keep_engine, (smartPunct_canon s).2]
  | unplaced =>
    rw [keep_unplaced, keep_unplaced]
    exact (smartPunct_canon s).1

end LeanTex.Core.Text

namespace LeanTex.Core.Elab

open Text Ir Parse

private theorem punctuationInline_canon (named : List Span) (o : Origin) (s : String) :
    canon (keep named (locatedOne o (punctuationInline false none s))) =
      canon (keep named (locatedOne o (.text s))) := by
  unfold punctuationInline
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · simp only [locatedOne_text]
    exact chars_smart named o s

private theorem mapSmartTextList_exact (acc : Array Inline) (l : List Inline) :
    mapSmartTextList none acc l = acc ++ (l.map (mapSmartText none)).toArray := by
  induction l generalizing acc with
  | nil => simp [mapSmartTextList]
  | cons x rest ih => simp [mapSmartTextList, ih]

mutual

private theorem mapSmartText_canon (named : List Span) (o : Origin) (x : Inline) :
    canon (keep named (locatedOne o (mapSmartText none x))) =
      canon (keep named (locatedOne o x)) := by
  match x with
  | .text s => exact punctuationInline_canon named o s
  | .role n inner =>
    simp only [mapSmartText, locatedOne_role, mapSmartTextList_exact, Array.empty_append]
    exact mapSmartTextList_canon named o inner.toList
  | .located sp inner =>
    simp only [mapSmartText, locatedOne_located, mapSmartTextList_exact, Array.empty_append]
    exact mapSmartTextList_canon named _ inner.toList
  | .math .. | .formula .. | .styled .. | .colored .. | .link .. | .label .. | .ref ..
  | .decorated .. | .boxed .. | .fill | .hspace .. | .rule .. | .pageNumber | .pageCount
  | .linebreak .. | .strut .. | .italicCorr .. | .onSteps .. | .altSteps .. | .image ..
  | .icon .. | .cite .. | .cited .. | .footnote .. => rfl

private theorem mapSmartTextList_canon (named : List Span) (o : Origin) :
    ∀ l : List Inline, canon (keep named (locatedList o (l.map (mapSmartText none)))) =
      canon (keep named (locatedList o l))
  | [] => rfl
  | x :: rest => by
    simp only [List.map_cons, locatedList_cons, keep_append, canon_append]
    rw [mapSmartText_canon named o x, mapSmartTextList_canon named o rest]

end

/-- Smart punctuation over a level's text reads as the text. -/
theorem view_mapSmartText (named : List Span) (xs : Array Inline) :
    view named (locatedText (xs.map (mapSmartText none))) = view named (locatedText xs) := by
  simp only [view, norm, locatedText, Array.toList_map]
  rw [mapSmartTextList_canon]

/-- The raws the plain-text arms of the inline knot read: words, spaces, paragraph breaks, symbols
and the control words `K` admits, whatever expansion marks them, and
groups, declaration scopes and input wrappers of them. -/
public inductive PlainRaw (K : String → Prop) : Parse.Raw → Prop
  | word (s : String) (p : Pos) : PlainRaw K (Parse.Raw.word s p)
  | space : PlainRaw K Parse.Raw.space
  | par (p : Pos) : PlainRaw K (Parse.Raw.par p)
  | sym (c : Char) (p : Pos) : PlainRaw K (Parse.Raw.sym c p)
  | group (body : Array Raw) (p : Pos) : (∀ r ∈ body, PlainRaw K r) →
      PlainRaw K (Parse.Raw.group body p)
  | scope (body : Array Raw) (p : Pos) : (∀ r ∈ body, PlainRaw K r) →
      PlainRaw K (Parse.Raw.env Parse.scopeEnv body p)
  | input (name file : String) (body : Array Raw) (p : Pos) :
      Parse.inputEnvFile? name = some file → (∀ r ∈ body, PlainRaw K r) →
      PlainRaw K (Parse.Raw.env name body p)
  | ctrl (name : String) (p : Pos) : K name → PlainRaw K (Parse.Raw.ctrl name p)

/-- A control word the inline knot sets as its own text whatever follows it: `\hfill`, `\par`,
or an escape or text symbol no accent shares, read under its own name. -/
@[expose] public def PlainCtrl (name : String) : Prop :=
  Compat.overlayName name = name ∧ (TextSymData.accents.map (·.1)).contains name = false ∧
    (name = "hfill" ∨ name = "par" ∨
      (name ∉ ["addcontentsline", "addtocontents", "qedhere", "ensuremath", "\\"] ∧
        ((escapeOf name).isSome ∨ (Lex.textSymbols.lookup name).isSome)))

/-- A context the controls `K` names read as built-ins in: no parameter and no document command
takes one of their names. -/
@[expose] public def Fits (K : String → Prop) (ctx : Ctx) : Prop :=
  (∀ a ∈ ctx.args, ¬ K a.1) ∧ ∀ c ∈ ctx.user, ¬ K c.name

/-- An inline run accounts for the source text `src` after `pre`: the pieces its diagnostics add
are tokens of `src`, and once they are excused its text reads as `pre` then `src`. -/
@[expose] public def Accounts (file : String) (src : List Raw) (run : Array Inline × ESt)
    (st : ESt) (pre : List (Char × Origin)) : Prop :=
  ∃ added : List Span,
    run.2.diags.toList.flatMap Diag.piece = st.diags.toList.flatMap Diag.piece ++ added ∧
    (∀ s ∈ added, ∃ c s', Span.samePlace s s' ∧ (c, .source s') ∈ Parse.rawTextList file src) ∧
    ∀ named : List Span, (∀ s ∈ added, s ∈ named) →
      view named (locatedText run.1) = view named (pre ++ Parse.rawTextList file src)

private theorem accounts_prefix (file : String) (rs src : List Raw) (run : Array Inline × ESt)
    (st st1 : ESt) (pre pre' : List (Char × Origin)) (added0 : List Span)
    (h : Accounts file src run st1 pre')
    (hd : st1.diags.toList.flatMap Diag.piece = st.diags.toList.flatMap Diag.piece ++ added0)
    (hd0 : ∀ s ∈ added0, ∃ c s', Span.samePlace s s' ∧ (c, .source s') ∈ Parse.rawTextList file rs)
    (hview : ∀ named : List Span, (∀ s ∈ added0, s ∈ named) →
      ∀ tail, view named (pre' ++ tail) = view named (pre ++ Parse.rawTextList file rs ++ tail)) :
    Accounts file (rs ++ src) run st pre := by
  obtain ⟨added, hdiags, hsrc, hv⟩ := h
  refine ⟨added0 ++ added, ?_, ?_, ?_⟩
  · rw [hdiags, hd, List.append_assoc]
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨c, s', hp, hc⟩ := hd0 s hs
      exact ⟨c, s', hp, by rw [Parse.rawTextList_append]; exact List.mem_append_left _ hc⟩
    · obtain ⟨c, s', hp, hc⟩ := hsrc s hs
      exact ⟨c, s', hp, by rw [Parse.rawTextList_append]; exact List.mem_append_right _ hc⟩
  · intro named hn
    rw [hv named (fun s hs => hn s (List.mem_append_right _ hs)),
      hview named (fun s hs => hn s (List.mem_append_left _ hs))]
    simp only [Parse.rawTextList_append, List.append_assoc]

private theorem accounts_cons (file : String) (r : Raw) (src : List Raw) (run : Array Inline × ESt)
    (st st1 : ESt) (pre pre' : List (Char × Origin)) (added0 : List Span)
    (h : Accounts file src run st1 pre')
    (hd : st1.diags.toList.flatMap Diag.piece = st.diags.toList.flatMap Diag.piece ++ added0)
    (hd0 : ∀ s ∈ added0, ∃ c s', Span.samePlace s s' ∧ (c, .source s') ∈ Parse.rawTextOne file r)
    (hview : ∀ named : List Span, (∀ s ∈ added0, s ∈ named) →
      ∀ tail, view named (pre' ++ tail) = view named (pre ++ Parse.rawTextOne file r ++ tail)) :
    Accounts file (r :: src) run st pre := by
  have hone : Parse.rawTextList file [r] = Parse.rawTextOne file r := by
    simp [Parse.rawTextList_cons]
  exact accounts_prefix file [r] src run st st1 pre pre' added0 h hd (by simpa [hone] using hd0)
    (by simpa [hone] using hview)

private theorem drop_skipSpaces (raws : Array Raw) (i : Nat) :
    ∃ k, raws.toList.drop i = List.replicate k .space ++ raws.toList.drop (skipSpaces raws i) := by
  fun_induction skipSpaces raws i with
  | case1 i h hs ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    have hl : i < raws.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hl, hk]
    have : raws.toList[i] = .space := by
      simp only [Array.getElem_toList]
      revert hs
      cases raws[i] <;> simp
    rw [this, List.replicate_succ, List.cons_append]
  | case2 => exact ⟨0, by simp⟩
  | case3 => exact ⟨0, by simp⟩

private theorem locatedText_flushText (acc : Array Inline) (sb : String) :
    locatedText (flushText acc sb) = locatedText acc ++ chars .unplaced sb := by
  unfold flushText
  split
  · rename_i h
    have : sb = "" := by simpa using h
    subst this
    simp [chars]
  · simp [locatedText_push]

private theorem locatedText_split (acc : Array Inline) (k : Nat) :
    locatedText acc = locatedText (acc.extract 0 k) ++ locatedText (acc.extract k acc.size) := by
  rw [← locatedText_append, Array.extract_append_extract]
  have : acc.extract 0 (max k acc.size) = acc := by
    rw [Array.extract_eq_self_iff]
    omega
  simp [this]

private theorem closeMacroRuns_located (acc : Array Inline) (runs : List MacroRun) :
    locatedText (closeMacroRuns macroRunInlines acc runs) = locatedText acc := by
  induction runs generalizing acc with
  | nil => rfl
  | cons run rest ih =>
    simp only [closeMacroRuns]
    rw [ih]
    split
    · rw [locatedText_split acc run.start, locatedText_append]
      simp [macroRunInlines, locatedText, locatedList_cons]
    · rfl

private theorem moveMacroRuns_located (active : Array MacroRun) (desired : List MacroOrigin)
    (acc : Array Inline) (pending : Bool) :
    locatedText (moveMacroRuns macroRunInlines active desired acc pending).2 = locatedText acc := by
  simp only [moveMacroRuns, closeMacroRuns_located]

private theorem step_located (c : Bool) (roles roles' : MacroRoles) (acc acc2 : Array Inline)
    (sb : String) (h : locatedText acc2 = locatedText (flushText acc sb)) :
    locatedText (if c then (roles, acc, sb) else (roles', acc2, "")).2.1 ++
        chars .unplaced (if c then (roles, acc, sb) else (roles', acc2, "")).2.2 =
      locatedText acc ++ chars .unplaced sb := by
  cases c <;> simp [h, locatedText_flushText]

/-- Moving the macro runs at a token only wraps what is set under roles. -/
private theorem inlineMacroStep_located (roles : MacroRoles) (raw : Option Raw)
    (acc : Array Inline) (sb : String) (following : List MacroOrigin) :
    locatedText (inlineMacroStep roles raw acc sb following).2.1 ++
        chars .unplaced (inlineMacroStep roles raw acc sb following).2.2 =
      locatedText acc ++ chars .unplaced sb := by
  unfold inlineMacroStep
  dsimp only
  exact step_located _ _ _ _ _ _ (moveMacroRuns_located _ _ _ _)

private theorem inlineMacroAt_located (roles : MacroRoles) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) :
    locatedText (inlineMacroAt roles raws i acc sb).2.1 ++
        chars .unplaced (inlineMacroAt roles raws i acc sb).2.2 =
      locatedText acc ++ chars .unplaced sb :=
  inlineMacroStep_located _ _ _ _ _

private theorem ends_space (t : String) (h : t.endsWith " " = true) :
    ∃ u, t.toList = u ++ [' '] := by
  have h' : t.toSlice.endsWith " " = true := by rw [String.endsWith_toSlice]; exact h
  rw [String.Slice.endsWith_string_iff] at h'
  obtain ⟨u, hu⟩ := h'
  exact ⟨u, by simpa using hu.symm⟩

private theorem view_space_after (named : List Span) (x tail : List (Char × Origin))
    (h : ∃ y, x = y ++ [(' ', .unplaced)]) :
    view named (x ++ (' ', .unplaced) :: tail) = view named (x ++ tail) := by
  obtain ⟨y, rfl⟩ := h
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    view_space_run named y tail

private theorem chars_ends (sb : String) (h : sb.endsWith " " = true) :
    ∃ y, chars .unplaced sb = y ++ [(' ', .unplaced)] := by
  obtain ⟨u, hu⟩ := ends_space sb h
  exact ⟨u.map (·, .unplaced), by simp [chars, hu]⟩

/-- A pending space's reading: one space, or none against a space already pending. -/
private theorem view_pending_space (named : List Span) (l : List (Char × Origin)) (sb : String)
    (tail : List (Char × Origin)) :
    view named ((l ++ chars .unplaced (if spaceSeps sb then sb.push ' ' else sb)) ++ tail) =
      view named (l ++ chars .unplaced sb ++ [(' ', .unplaced)] ++ tail) := by
  split
  · simp [chars, List.append_assoc]
  · rename_i hs
    have he : sb.endsWith " " = true := by simpa [spaceSeps] using hs
    have := view_space_after named (l ++ chars .unplaced sb) tail
      (by obtain ⟨y, hy⟩ := chars_ends sb he; exact ⟨l ++ y, by simp [hy]⟩)
    simpa [chars] using this.symm

private theorem inputEnvFile?_scope : Parse.inputEnvFile? Parse.scopeEnv = none := by
  simp [Parse.inputEnvFile?, Parse.scopeEnv]

private theorem inputEnvFile?_mode : Parse.inputEnvFile? Parse.modeEnv = none := by
  simp [Parse.inputEnvFile?, Parse.modeEnv]

private theorem core_plain (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (h : ∀ st, Accounts ctx.file (raws.toList.drop 0)
      ((elabInlinesFrom { { ctx with macroRoles := ctx.macroRoles.enter } with
        callSite := none, literalWhen := none } raws 0 #[] "").run st) st
      (locatedText #[] ++ chars .unplaced "")) :
    Accounts ctx.file raws.toList
      ((elabInlinesCore { ctx with callSite := none, literalWhen := none } raws).run st) st [] := by
  have hrun : (elabInlinesCore { ctx with callSite := none, literalWhen := none } raws).run st =
      (if ctx.literalText then
        ((elabInlinesFrom { { ctx with macroRoles := ctx.macroRoles.enter } with
          callSite := none, literalWhen := none } raws 0 #[] "").run st).1
      else ((elabInlinesFrom { { ctx with macroRoles := ctx.macroRoles.enter } with
          callSite := none, literalWhen := none } raws 0 #[] "").run st).1.map (mapSmartText none),
        ((elabInlinesFrom { { ctx with macroRoles := ctx.macroRoles.enter } with
          callSite := none, literalWhen := none } raws 0 #[] "").run st).2) := by
    rw [elabInlinesCore]
    rfl
  rw [hrun]
  obtain ⟨new, hd, hk, hv⟩ := h st
  simp only [List.drop_zero] at hk hv
  refine ⟨new, hd, hk, fun named hn => ?_⟩
  have := hv named hn
  simp only [locatedText_empty, chars_empty, List.nil_append] at this
  dsimp only
  split
  · exact this
  · rw [view_mapSmartText]
    exact this

private theorem core_enter (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (hsite : ctx.callSite = none) (hwhen : ctx.literalWhen = none)
    (h : ∀ st, Accounts ctx.file (raws.toList.drop 0)
      ((elabInlinesFrom { { ctx with macroRoles := ctx.macroRoles.enter } with
        callSite := none, literalWhen := none } raws 0 #[] "").run st) st
      (locatedText #[] ++ chars .unplaced "")) :
    Accounts ctx.file raws.toList ((elabInlinesCore ctx raws).run st) st [] := by
  have hctx : ctx = { ctx with callSite := none, literalWhen := none } := by
    cases ctx
    simp_all
  rw [hctx]
  exact core_plain ctx raws st h

private theorem accounts_inner (file innerFile : String) (r : Raw) (body : Array Raw)
    (src : List Raw) (run : Array Inline × ESt) (st stI st1 : ESt) (pre : List (Char × Origin))
    (inner : Array Inline) (hI : Accounts innerFile body.toList (inner, stI) st [])
    (hr : Parse.rawTextOne file r = Parse.rawTextList innerFile body.toList)
    (hst : st1.diags = stI.diags) (h : Accounts file src run st1 (pre ++ locatedText inner)) :
    Accounts file (r :: src) run st pre := by
  obtain ⟨newI, hdI, hkI, hvI⟩ := hI
  refine accounts_cons file r src run st st1 pre _ newI h (by rw [hst]; exact hdI) ?_ ?_
  · intro s hs
    rw [hr]
    exact hkI s hs
  · intro named hn tail
    rw [hr, List.append_assoc, List.append_assoc]
    have hv := hvI named hn
    simp only [List.nil_append] at hv
    exact view_congr named rfl (view_congr named hv rfl)

private theorem run_group (base : Palette) (act : EM (Array Inline)) (k : Array Inline → EM α)
    (st : ESt) :
    ((do let x ← inlineGroup base act; k x) : EM α).run st =
      (k (act.run st).1).run
        { (act.run st).2 with scope := st.scope.restore base (act.run st).2.scope } :=
  rfl

private theorem run_bind' (act : EM β) (k : β → EM α) (st : ESt) :
    ((do let x ← act; k x) : EM α).run st = (k (act.run st).1).run (act.run st).2 :=
  rfl

private theorem pre_inner (acc inner : Array Inline) (sb : String) :
    locatedText (flushText acc sb ++ inner) ++ chars .unplaced "" =
      locatedText acc ++ chars .unplaced sb ++ locatedText inner := by
  simp [locatedText_append, locatedText_flushText]

private theorem wordAfter_canon (ctx : Ctx) (acc : Array Inline) (sb w : String) :
    canon (wordAfter ctx acc sb w).toList = canon w.toList ∧
      (wordAfter ctx acc sb w).toList.filter (·.isWhitespace) =
        w.toList.filter (·.isWhitespace) := by
  unfold wordAfter
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact smartPunctAfter_canon _ _
    · exact ⟨rfl, rfl⟩

private theorem slice_body {raws body : Array Raw} {i : Nat} (h : i < raws.size)
    (hb : rawWeightList body.toList < rawWeight raws[i]) :
    sliceWeight body 0 < sliceWeight raws i := by
  have := body_lt_slice' h hb
  simpa [sliceWeight] using this

private theorem find_args_none (K : String → Prop) (ctx : Ctx) (name : String) (hfit : Fits K ctx)
    (hk : K name) : ctx.args.find? (fun x => x.fst == name) = none := by
  rw [Array.find?_eq_none]
  intro a ha he
  simp only [beq_iff_eq] at he
  exact hfit.1 a ha (he ▸ hk)

private theorem latestNamed_mem {α : Type} {nameOf : α → String} {xs : Array α} {want : String}
    {n k : Nat} {x : α} (h : latestNamed nameOf xs want n = some (k, x)) :
    x ∈ xs ∧ nameOf x = want := by
  fun_induction latestNamed nameOf xs want n with
  | case1 => simp at h
  | case2 k hk hn =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨Array.getElem_mem hk, by simpa using hn⟩
  | case3 _ _ _ ih => exact ih h
  | case4 _ _ ih => exact ih h

private theorem lookupUser_fits (K : String → Prop) (ctx : Ctx) (name : String) (hfit : Fits K ctx)
    (hk : K name) : lookupUser ctx name = none := by
  unfold lookupUser
  split
  · rfl
  · cases hl : latestNamed (·.name) ctx.user name ctx.limit with
    | none => rfl
    | some x =>
      obtain ⟨hm, hn⟩ := latestNamed_mem hl
      exact absurd (hn ▸ hk) (hfit.2 _ hm)

/-- What the spine owes at `raws`, `i`: its run accounts for the raws from `i`. -/
private def SpineAccounts (ctx : Ctx) (raws : Array Raw) (i : Nat) (acc : Array Inline)
    (sb : String) (st : ESt) : Prop :=
  Accounts ctx.file (raws.toList.drop i)
    ((elabInlinesFrom { ctx with callSite := none, literalWhen := none } raws i acc sb).run st) st
    (locatedText acc ++ chars .unplaced sb)

/-- One step of the spine, the steps after it lighter. -/
private theorem spine_step (K : String → Prop) (hK : ∀ n, K n → PlainCtrl n) (ctx : Ctx)
    (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String) (st : ESt) (hfit : Fits K ctx)
    (hr : ∀ r ∈ raws, PlainRaw K r)
    (ih : ∀ (ctx' : Ctx) (raws' : Array Raw) (i' : Nat) (acc' : Array Inline) (sb' : String)
      (st' : ESt), sliceWeight raws' i' < sliceWeight raws i → Fits K ctx' →
      (∀ r ∈ raws', PlainRaw K r) → SpineAccounts ctx' raws' i' acc' sb' st') :
    Accounts ctx.file (raws.toList.drop i)
      ((elabInlinesFrom { ctx with callSite := none, literalWhen := none } raws i acc sb).run st) st
      (locatedText acc ++ chars .unplaced sb) := by
  rw [elabInlinesFrom]
  have hstep := inlineMacroAt_located
    ({ ctx with callSite := none, literalWhen := none } : Ctx).macroRoles raws i acc sb
  generalize inlineMacroAt
    ({ ctx with callSite := none, literalWhen := none } : Ctx).macroRoles raws i acc sb = state
    at hstep ⊢
  rcases state with ⟨roles, acc', sb'⟩
  dsimp only at hstep ⊢
  rw [← hstep]
  clear hstep
  by_cases h : i < raws.size
  · rw [dite_eq_left h]
    have hnext := sliceWeight_lt raws h (Nat.lt_succ_self i)
    have hx := hr raws[i] (Array.getElem_mem h)
    have hdrop : raws.toList.drop i = raws[i] :: raws.toList.drop (i + 1) := by
      have hl : i < raws.toList.length := by simpa using h
      rw [List.drop_eq_getElem_cons hl]
      simp
    rw [hdrop]
    have hgroup : ∀ {body : Array Raw} {p : Pos}, raws[i] = .group body p →
        sliceWeight body 0 < sliceWeight raws i := by
      intro body p hb
      apply slice_body h
      rw [hb]
      simp only [rawWeight]
      omega
    have henv : ∀ {name : String} {body : Array Raw} {p : Pos}, raws[i] = .env name body p →
        sliceWeight body 0 < sliceWeight raws i := by
      intro name body p hb
      apply slice_body h
      rw [hb]
      simp only [rawWeight]
      omega
    split
    all_goals rename_i heq
    all_goals rw [heq] at hx
    all_goals cases hx
    all_goals rw [heq]
    case h_1.word s p =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr)
        (by simp) (by simp) ?_
      intro named _ tail
      simp only [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
        locatedOne_located, locatedOne_text, locatedList_cons, locatedList_nil,
        Parse.rawTextOne_word, Option.map_none, Option.getD_none, List.append_nil,
        List.append_assoc, chars_empty]
      rw [← List.append_assoc (locatedText acc'), ← List.append_assoc (locatedText acc')]
      exact view_token named _ (wordAfter_canon _ _ _ _).1 _ _
    case h_2.space =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) acc' _ st hnext hfit hr)
        (by simp) (by simp) ?_
      intro named _ tail
      simp only [Parse.rawTextOne_space]
      exact view_pending_space named _ sb' tail
    case h_3.par p =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) acc' _ st hnext hfit hr)
        (by simp) (by simp) ?_
      intro named _ tail
      simp only [Parse.rawTextOne_par]
      split
      · simp [chars, List.append_assoc]
      · rename_i hs
        unfold needsSep at hs
        split at hs
        · rename_i hsb
          have hsb' : sb' = "" := by simpa using hsb
          subst hsb'
          split at hs
          · rename_i t hb
            have he : t.endsWith " " = true := by simpa using hs
            obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hb
            obtain ⟨y, hy⟩ := chars_ends t he
            have := view_space_after named (locatedText (ys.push (.text t))) tail
              ⟨locatedText ys ++ y, by simp [locatedText_push, hy]⟩
            simpa [chars] using this.symm
          · simp at hs
        · have he : sb'.endsWith " " = true := by simpa using hs
          have := view_space_after named (locatedText acc' ++ chars .unplaced sb') tail
            (by obtain ⟨y, hy⟩ := chars_ends sb' he; exact ⟨locatedText acc' ++ y, by simp [hy]⟩)
          simpa [chars] using this.symm
    case h_12.ctrl name p hk =>
      have hfit' : Fits K ({ { ctx with callSite := none, literalWhen := none } with
          macroRoles := roles } : Ctx) := hfit
      rw [find_args_none K _ name hfit' hk]
      split
      · rename_i hu
        cases hu
      split
      · rename_i hu
        rw [lookupUser_fits K _ name hfit' hk] at hu
        cases hu
      obtain ⟨hover, hacc, hcase⟩ := hK name hk
      simp only [hover]
      by_cases hhf : name = "hfill"
      · subst hhf
        simp only [show ("hfill" == "addcontentsline" || "hfill" == "addtocontents") = false by
            decide, show ("hfill" == "hfill") = true by decide, Bool.false_eq_true, ↓reduceIte]
        refine accounts_cons ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr)
          (by simp) (by simp) ?_
        intro named _ tail
        simp [locatedText_push, locatedText_flushText, locatedOne, locatedOnto, Parse.ctrlText,
          hover]
      by_cases hpar : name = "par"
      · subst hpar
        simp only [show ("par" == "addcontentsline" || "par" == "addtocontents") = false by decide,
          show ("par" == "hfill") = false by decide, show ("par" == "qedhere") = false by decide,
          show ("par" == "ensuremath") = false by decide,
          show ("par" == "\\") = false by decide, beq_self_eq_true, Bool.or_true,
          Bool.false_eq_true, ↓reduceIte]
        obtain ⟨k, hk'⟩ := drop_skipSpaces raws (i + 1)
        rw [hk', ← List.cons_append]
        have hj := Parse.skipSpaces_ge raws (i + 1)
        refine accounts_prefix ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (skipSpaces raws (i + 1)) _ "" st
            (sliceWeight_lt raws h (by omega)) hfit hr) (by simp) (by simp) ?_
        intro named _ tail
        simp only [locatedText_push, locatedText_flushText, chars_empty, List.append_nil,
          Parse.rawTextList_cons, Parse.rawTextOne_ctrl, Parse.ctrlText, hover, true_or, ↓reduceIte,
          List.append_assoc, List.cons_append, List.nil_append, Parse.rawTextList_spaces]
        have hl : locatedOne .unplaced (Inline.linebreak {}) = [(' ', .engine)] := rfl
        rw [hl, List.singleton_append, ← List.append_assoc, ← List.append_assoc,
          view_spaces, view_engine_space]
      obtain ⟨hnot, hown⟩ := hcase.resolve_left hhf |>.resolve_left hpar
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
      obtain ⟨n1, n2, n3, n4, n5⟩ := hnot
      have haccent : raws[i + 1]?.bind (accentCompose name) = none := by
        have hm : accentMarkOf name = none :=
          Std.HashMap.getElem?_ofList_of_contains_eq_false hacc
        cases raws[i + 1]? <;> simp [accentCompose, hm]
      simp only [beq_eq_false_iff_ne.mpr n1, beq_eq_false_iff_ne.mpr n2,
        beq_eq_false_iff_ne.mpr hhf, beq_eq_false_iff_ne.mpr n3, beq_eq_false_iff_ne.mpr n4,
        beq_eq_false_iff_ne.mpr n5, beq_eq_false_iff_ne.mpr hpar, haccent, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte]
      cases hesc : escapeOf name with
      | some lit =>
        simp only []
        by_cases hsp : name = " "
        · subst hsp
          have hlit : lit = " " := by
            have hl : escapes.lookup " " = some " " := by decide
            simp only [escapeOf, hl, Option.some.injEq] at hesc
            exact hesc.symm
          subst hlit
          simp only [beq_self_eq_true, ↓reduceIte]
          refine accounts_cons ctx.file _ _ _ st st _ _ []
            (ih { ctx with macroRoles := roles } raws (i + 1) acc' _ st hnext hfit hr)
            (by simp) (by simp) ?_
          intro named _ tail
          simp [Parse.ctrlText, hover, chars]
        · simp only [beq_eq_false_iff_ne.mpr hsp, Bool.false_eq_true, ↓reduceIte]
          refine accounts_cons ctx.file _ _ _ st st _ _ []
            (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr)
            (by simp) (by simp) ?_
          intro named _ tail
          simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
            locatedList_cons, Parse.ctrlText, hover, hesc, hhf, hpar, n5, hsp]
      | none =>
        have hsym : (Lex.textSymbols.lookup name).isSome = true := by
          simpa [hesc] using hown
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsym
        have hsp' : name ≠ " " := by
          rintro rfl
          have hl : escapes.lookup " " = some " " := by decide
          simp [escapeOf, hl] at hesc
        simp only [ht, Option.getD_some]
        refine accounts_cons ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr)
          (by simp) (by simp) ?_
        intro named _ tail
        simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
          locatedList_cons, Parse.ctrlText, hover, hesc, hhf, hpar, n5, hsp', ht]
    case h_4.sym p | h_5.sym p | h_6.sym p =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr)
        (by simp) (by simp) ?_
      intro named _ tail
      simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
        locatedList_cons, chars]
    case h_7.sym c p h1 h2 h3 =>
      have hc : c ≠ '~' := h3
      split
      · refine accounts_cons ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr)
          (by simp) (by simp) ?_
        intro named _ tail
        simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
          locatedList_cons, chars, hc]
      · refine accounts_cons ctx.file _ _ _ st _ _ _ [⟨ctx.file, p⟩]
          (ih { ctx with macroRoles := roles } raws (i + 1) acc' sb' _ hnext hfit hr) ?_ ?_ ?_
        · show (st.diags.push _).toList.flatMap Diag.piece = _
          have hloss : DiagCode.E0311.loss = .dropped := rfl
          simp [Diag.piece, diagOf, Diag.of, Ctx.sourceSpan, hloss]
        · intro s hs
          simp only [List.mem_singleton] at hs
          subst hs
          exact ⟨c, ⟨ctx.file, p⟩, Span.samePlace_self _, by simp [hc]⟩
        · intro named hn tail
          have hs : (⟨ctx.file, p⟩ : Span) ∈ named := hn _ (List.mem_singleton_self _)
          have := view_named named _ hs [c] (locatedText acc' ++ chars .unplaced sb') tail
          simpa [hc, List.append_assoc] using this.symm
    case h_9.group body p _ =>
      have hb : ∀ r ∈ body, PlainRaw K r := by assumption
      rw [run_group]
      refine accounts_inner ctx.file ctx.file _ body _ _ st _ _ _ _
        (core_plain { ctx with macroRoles := roles } body st fun st =>
          ih { ctx with macroRoles := roles.enter } body 0 #[] "" st (hgroup heq) hfit hb)
        (by simp) rfl ?_
      rw [← pre_inner]
      exact ih { ctx with macroRoles := roles } raws (i + 1) _ "" _ hnext hfit hr
    case h_10.scope body p _ =>
      have hb : ∀ r ∈ body, PlainRaw K r := by assumption
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [run_bind']
      refine accounts_inner ctx.file ctx.file _ body _ _ st _ _ _ _
        (core_plain { ctx with macroRoles := roles } body st fun st =>
          ih { ctx with macroRoles := roles.enter } body 0 #[] "" st (henv heq) hfit hb)
        (by simp [inputEnvFile?_scope]) rfl ?_
      rw [← pre_inner]
      exact ih { ctx with macroRoles := roles } raws (i + 1) _ "" _ hnext hfit hr
    case h_10.input name body p f _ _ =>
      have hb : ∀ r ∈ body, PlainRaw K r := by assumption
      have hf : Parse.inputEnvFile? name = some f := by assumption
      have hs : (name == Parse.scopeEnv) = false := by
        rw [beq_eq_false_iff_ne]
        rintro rfl
        rw [inputEnvFile?_scope] at hf
        cases hf
      have hmode : (name == Parse.modeEnv) = false := by
        rw [beq_eq_false_iff_ne]
        rintro rfl
        rw [inputEnvFile?_mode] at hf
        cases hf
      simp only [hs, hmode, hf, Bool.false_eq_true, ↓reduceIte]
      rw [run_bind']
      let base : Ctx := { ctx with macroRoles := roles, callSite := none, literalWhen := none }
      let ictx : Ctx := base.enterInput name f
      refine accounts_inner ctx.file f _ body _ _ st _ _ _ _
        (core_enter ictx body st rfl rfl fun st =>
          ih { ictx with macroRoles := roles.enter } body 0 #[] "" st (henv heq) hfit hb)
        (by simp [hf]) rfl ?_
      rw [← pre_inner]
      exact ih { ctx with macroRoles := roles } raws (i + 1) _ "" _ hnext hfit hr
  · simp only [h, ↓reduceDIte]
    have hdrop : raws.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using Nat.not_lt.mp h)
    rw [hdrop]
    refine ⟨[], by rw [List.append_nil]; rfl, by simp, fun named _ => ?_⟩
    show view named (locatedText (mergeTexts (flushText acc' sb'))) = _
    rw [locatedText_mergeTexts, locatedText_flushText]
    simp

private theorem spine_plain (K : String → Prop) (hK : ∀ n, K n → PlainCtrl n) (ctx : Ctx)
    (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String) (st : ESt) (hfit : Fits K ctx)
    (hr : ∀ r ∈ raws, PlainRaw K r) :
    SpineAccounts ctx raws i acc sb st := by
  have key : ∀ n (ctx : Ctx) (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String)
      (st : ESt), sliceWeight raws i = n → Fits K ctx → (∀ r ∈ raws, PlainRaw K r) →
      SpineAccounts ctx raws i acc sb st := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ctx raws i acc sb st hn hfit hr
      exact spine_step K hK ctx raws i acc sb st hfit hr
        fun ctx' raws' i' acc' sb' st' hlt hfit' hr' =>
          ih _ (hn ▸ hlt) ctx' raws' i' acc' sb' st' rfl hfit' hr'
  exact key _ ctx raws i acc sb st rfl hfit hr

/-- The plain-text arms of the inline knot conserve the source's text: once the reserved
characters it refuses are excused, a run of words, spaces, breaks and symbols, through groups,
declaration scopes and input wrappers, reads as its source. -/
public theorem elabInlines_plain_text (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (hsite : ctx.callSite = none) (hwhen : ctx.literalWhen = none)
    (hr : ∀ r ∈ raws, PlainRaw (fun _ => False) r) :
    Accounts ctx.file raws.toList ((elabInlines ctx raws).run st) st [] := by
  rw [elabInlines]
  exact core_enter ctx raws st hsite hwhen fun st =>
    spine_plain _ (fun _ h => h.elim) { ctx with macroRoles := ctx.macroRoles.enter } raws 0 #[]
      "" st ⟨fun _ _ h => h, fun _ _ h => h⟩ hr

/-- Control words that set their own text conserve it too: with no parameter or document command
taking their names, `\hfill`, `\par`, and escapes and text symbols no accent shares read as their
source among the plain-text arms. -/
public theorem elabInlines_ctrl_text (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (hsite : ctx.callSite = none) (hwhen : ctx.literalWhen = none) (hfit : Fits PlainCtrl ctx)
    (hr : ∀ r ∈ raws, PlainRaw PlainCtrl r) :
    Accounts ctx.file raws.toList ((elabInlines ctx raws).run st) st [] := by
  rw [elabInlines]
  exact core_enter ctx raws st hsite hwhen fun st =>
    spine_plain _ (fun _ h => h) { ctx with macroRoles := ctx.macroRoles.enter } raws 0 #[] "" st
      hfit hr

end LeanTex.Core.Elab
