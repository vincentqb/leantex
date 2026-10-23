module

public import LeanTex.Core.TextAccount
public import LeanTex.Core.Elab
public import LeanTex.Core.TextSymData

import all LeanTex.Core.Ir
import all LeanTex.Core.Elab
import all LeanTex.Core.Parse
import all LeanTex.Core.Diag
import all LeanTex.Core.TextSymData
import all LeanTex.Core.BibAccent

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
    canon (Ir.smartPunctAfter lead s).toList = canon s.toList := by
  cases lead with
  | none => exact (smartPunct_canon s).1
  | some c =>
    obtain ⟨x, hx, hs, _⟩ := smartPunct_go_canon s.toList [c]
    simp [Ir.smartPunctAfter, hx, hs]

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
  | .icon .. | .cite .. | .cited .. | .footnote .. | .marginNote .. => rfl

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

/-- Each control `M` names stands directly before its braced argument, and `\emph` before no
overlay word after it. -/
@[expose] public def ModArgs (M : String → Prop) (raws : Array Raw) : Prop :=
  ∀ (i : Nat) (name : String) (p : Pos), raws[i]? = some (.ctrl name p) → M name →
    (∃ body q, raws[i + 1]? = some (.group body q)) ∧
      (name = "emph" → (raws[i + 2]?.bind Compat.overlayWord?) = none)

/-- The raws the plain-text arms of the inline knot read: words, spaces, paragraph breaks, symbols,
the control words `K` admits and the argument-taking ones `M` admits, whatever expansion marks
them, and groups, declaration scopes and input wrappers of them. -/
public inductive PlainRaw (K M : String → Prop) : Parse.Raw → Prop
  | word (s : String) (p : Pos) : PlainRaw K M (Parse.Raw.word s p)
  | space : PlainRaw K M Parse.Raw.space
  | par (p : Pos) : PlainRaw K M (Parse.Raw.par p)
  | sym (c : Char) (p : Pos) : PlainRaw K M (Parse.Raw.sym c p)
  | group (body : Array Raw) (p : Pos) : ModArgs M body → (∀ r ∈ body, PlainRaw K M r) →
      PlainRaw K M (Parse.Raw.group body p)
  | scope (body : Array Raw) (p : Pos) : ModArgs M body → (∀ r ∈ body, PlainRaw K M r) →
      PlainRaw K M (Parse.Raw.env Parse.scopeEnv body p)
  | input (name file : String) (body : Array Raw) (p : Pos) :
      Parse.inputEnvFile? name = some file → ModArgs M body → (∀ r ∈ body, PlainRaw K M r) →
      PlainRaw K M (Parse.Raw.env name body p)
  | ctrl (name : String) (p : Pos) : K name → PlainRaw K M (Parse.Raw.ctrl name p)
  | mod (name : String) (p : Pos) : M name → PlainRaw K M (Parse.Raw.ctrl name p)

/-- A control word the inline knot sets as its own text whatever follows it: `\hfill`, `\par`,
or an escape or text symbol no accent shares, read under its own name. -/
@[expose] public def PlainCtrl (name : String) : Prop :=
  Compat.overlayName name = name ∧ (TextSymData.accents.map (·.1)).contains name = false ∧
    (name = "hfill" ∨ name = "par" ∨
      (name ∉ ["addcontentsline", "addtocontents", "qedhere", "ensuremath", "\\"] ∧
        ((escapeOf name).isSome ∨ (Lex.textSymbols.lookup name).isSome)))

/-- A command setting its argument under a text font or a decoration: `\textbf`, `\emph` and the
other NFSS spellings, `\underline`, `\uline` and `\sout`. -/
@[expose] public def ModCtrl (name : String) : Prop :=
  name ∈ argStyles.map (·.1) ++ ["underline", "uline", "sout"]

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
    canon (wordAfter ctx acc sb w).toList = canon w.toList := by
  unfold wordAfter
  split
  · rfl
  · split
    · exact smartPunctAfter_canon _ _
    · rfl

private theorem slice_body {raws body : Array Raw} {i : Nat} (h : i < raws.size)
    (hb : rawWeightList body.toList < rawWeight raws[i]) :
    sliceWeight body 0 < sliceWeight raws i := by
  have := body_lt_slice' h hb
  simpa [sliceWeight] using this

private theorem escapeOf_space : escapeOf " " = some " " := by
  have hl : escapes.lookup " " = some " " := by decide
  simp only [escapeOf, hl]

private theorem markNames_unspelled :
    ∀ n ∈ ["markboth", "markright", "leftmark", "rightmark"],
      escapes.lookup n = none ∧ Bib.charCommands.find? (·.1 == n) = none ∧
        Lex.textSymbols.lookup n = none ∧ (TextSymData.symbols.map (·.1)).contains n = false := by
  decide +kernel

private theorem unspelled_not_lineCtrl (name : String)
    (h : (escapeOf name).isSome ∨ (Lex.textSymbols.lookup name).isSome)
    (n1 : name ≠ "addcontentsline") (n2 : name ≠ "addtocontents") :
    (lineCtrl name || name == "leftmark" || name == "rightmark") = false := by
  rw [Bool.eq_false_iff]
  intro hb
  simp only [lineCtrl, markCtrl, Bool.or_eq_true, beq_iff_eq] at hb
  have hmem : name ∈ ["markboth", "markright", "leftmark", "rightmark"] := by
    rcases hb with (((h1 | h1) | h1 | h1) | h1) | h1 <;> simp_all
  obtain ⟨he, hc, ht, hs⟩ := markNames_unspelled name hmem
  have hsym : textSymbolMap[name]? = none := Std.HashMap.getElem?_ofList_of_contains_eq_false hs
  simp [escapeOf, he, hc, ht, hsym] at h

private theorem find_args_none (K : String → Prop) (ctx : Ctx) (name : String) (hfit : Fits K ctx)
    (hk : K name) : ctx.args.find? (fun x => x.fst == name) = none := by
  rw [Array.find?_eq_none]
  intro a ha he
  simp only [beq_iff_eq] at he
  exact hfit.1 a ha (he ▸ hk)

private theorem latestNamed_named {α : Type} {nameOf : α → String} {xs : Array α} {want : String}
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
      obtain ⟨hm, hn⟩ := latestNamed_named hl
      exact absurd (hn ▸ hk) (hfit.2 _ hm)

/-- What the spine owes at `raws`, `i`: its run accounts for the raws from `i`. -/
private def SpineAccounts (ctx : Ctx) (raws : Array Raw) (i : Nat) (acc : Array Inline)
    (sb : String) (st : ESt) : Prop :=
  Accounts ctx.file (raws.toList.drop i)
    ((elabInlinesFrom { ctx with callSite := none, literalWhen := none } raws i acc sb).run st) st
    (locatedText acc ++ chars .unplaced sb)

private abbrev modNames : List String := argStyles.map (·.1) ++ ["underline", "uline", "sout"]

private theorem decorationCtrls_names : decorationCtrls.map (·.1) = ["underline", "uline", "sout"] :=
  rfl

private theorem modNames_spelled :
    ∀ n ∈ modNames, Compat.overlayName n = n ∧ theCounterName? n = none := by
  simp [modNames, argStyles, fontAxes, Compat.overlayName_plain, theCounterName?]

private theorem modNames_accent :
    ∀ n ∈ modNames, (TextSymData.accents.map (·.1)).contains n = false := by
  decide +kernel

private theorem modNames_symbol :
    ∀ n ∈ modNames, (TextSymData.symbols.map (·.1)).contains n = false := by
  decide +kernel

private theorem modNames_escape :
    ∀ n ∈ modNames, escapes.lookup n = none ∧ Bib.charCommands.find? (·.1 == n) = none ∧
      Lex.textSymbols.lookup n = none := by
  decide +kernel

private theorem modNames_guards :
    ∀ n ∈ modNames, lineCtrl n = false ∧
      n ∉ ["leftmark", "rightmark", "hfill", "qedhere", "ensuremath", "\\", "par", " ", "nocorr",
        "alert themed", "alert plain"] := by
  decide +kernel

private theorem modNames_kind :
    ∀ n ∈ modNames, (argStyles.lookup n).isSome ∨
      (argStyles.lookup n = none ∧ (decorationCtrls.lookup n).isSome) := by
  decide +kernel

private structure ModFacts (name : String) : Prop where
  over : Compat.overlayName name = name
  accent : accentMarkOf name = none
  esc : escapeOf name = none
  sym : Lex.textSymbols.lookup name = none
  counter : theCounterName? name = none
  line : (lineCtrl name || name == "leftmark" || name == "rightmark") = false
  hfill : (name == "hfill") = false
  qed : (name == "qedhere") = false
  ensure : (name == "ensuremath") = false
  brk : (name == "\\" || name == "par") = false
  alertT : (name == Compat.alertMark true) = false
  alertF : (name == Compat.alertMark false) = false
  text : ∀ file p, Parse.ctrlText file name p = []
  kind : (∃ st, modifierStyle? name = some st) ∨
    (modifierStyle? name = none ∧ ∃ d, decorationCtrls.lookup name = some d)

private theorem modFacts (name : String) (h : ModCtrl name) : ModFacts name := by
  obtain ⟨ho, hctr⟩ := modNames_spelled name h
  have ha := modNames_accent name h
  have hs := modNames_symbol name h
  obtain ⟨he, hc, ht⟩ := modNames_escape name h
  obtain ⟨hl, hnot⟩ := modNames_guards name h
  have hst := modNames_kind name h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, _, n10, n11⟩ := hnot
  have hsym : textSymbolMap[name]? = none := Std.HashMap.getElem?_ofList_of_contains_eq_false hs
  refine ⟨ho, Std.HashMap.getElem?_ofList_of_contains_eq_false ha, by simp [escapeOf, he, hc, hsym],
    ht, hctr, by simp [hl, n1, n2], by simp [n3], by simp [n4], by simp [n5], by simp [n6, n7],
    by simp [Compat.alertMark_eq, n10], by simp [Compat.alertMark_eq, n11],
    fun _ _ => by simp [Parse.ctrlText, ho, n3, n6, n7, n8, escapeOf, he, hc, hsym, ht], ?_⟩
  rcases hst with hst | ⟨hnone, hd⟩
  · obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hst
    exact .inl ⟨st, by simp [modifierStyle?, Compat.alertMark_eq, n10, n11, hst]⟩
  · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hd
    exact .inr ⟨by simp [modifierStyle?, Compat.alertMark_eq, n10, n11, hnone], d, hd⟩

private theorem nocorr_not_plain : ¬ PlainCtrl "nocorr" ∧ ¬ ModCtrl "nocorr" := by
  refine ⟨fun ⟨_, _, h⟩ => ?_, fun h => ?_⟩
  · have he : escapeOf "nocorr" = none := by
      have hs : (TextSymData.symbols.map (·.1)).contains "nocorr" = false := by decide +kernel
      have hsym : textSymbolMap["nocorr"]? = none :=
        Std.HashMap.getElem?_ofList_of_contains_eq_false hs
      have h1 : escapes.lookup "nocorr" = none := by decide +kernel
      have h2 : Bib.charCommands.find? (·.1 == "nocorr") = none := by decide +kernel
      simp [escapeOf, h1, h2, hsym]
    have ht : Lex.textSymbols.lookup "nocorr" = none := by decide +kernel
    simp [he, ht] at h
  · exact (modNames_guards _ h).2 (by simp)

private theorem locatedText_fontCmdInlines (style : Style) (edges : Bool × Bool)
    (inner : Array Inline) : locatedText (Ir.fontCmdInlines style edges inner) = locatedText inner := by
  have hs : ∀ body : Array Inline, locatedText #[.styled style body] = locatedText body := by
    intro body
    rfl
  have hc : locatedText #[Inline.italicCorr true] = [] := rfl
  unfold Ir.fontCmdInlines
  split <;> split <;>
    simp only [hs, locatedText_append, hc, List.nil_append, List.append_nil,
      show ∀ x y : Inline, (#[x, y] : Array Inline) = #[x] ++ #[y] from fun _ _ => rfl]

private theorem modifierLiteral_none_when (c : Ctx) (style : Style) (h : c.literalWhen = none) :
    (modifierLiteral c style none).2 = none := by
  unfold modifierLiteral
  split
  · exact h
  · exact h

private theorem fontCmdContent_plain (K M : String → Prop) (hK : ∀ n, K n → PlainCtrl n)
    (hM : ∀ n, M n → ModCtrl n) (body : Array Raw) (hb : ∀ r ∈ body, PlainRaw K M r) :
    fontCmdContent body = body := by
  unfold fontCmdContent
  rw [Array.filter_eq_self]
  intro r hr
  have := hb r hr
  cases this with
  | ctrl name p hk =>
    have := hK name hk
    by_cases hn : name = "nocorr"
    · subst hn
      exact absurd this nocorr_not_plain.1
    · simp [fontCmdNocorr, hn]
  | mod name p hk =>
    have := hM name hk
    by_cases hn : name = "nocorr"
    · subst hn
      exact absurd this nocorr_not_plain.2
    · simp [fontCmdNocorr, hn]
  | _ => simp [fontCmdNocorr]

private theorem modifierInlines_plain (name : String) (F : ModFacts name) (c : Ctx) (style : Style)
    (edges : Bool × Bool) (inner : Array Inline) (p : Pos) (s0 : ESt) :
    (modifierInlines c name style edges inner p).run s0 = (Ir.fontCmdInlines style edges inner, s0) := by
  unfold modifierInlines
  simp only [F.alertF, bne, F.alertT, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A command wrapping its braced argument accounts for both raws as the argument. -/
private theorem arg_tail (file name : String) (p q : Pos) (body : Array Raw) (rest : List Raw)
    (run : Array Inline × ESt) (st stI : ESt) (acc' inner W : Array Inline) (sb' : String)
    (hI : Accounts file body.toList (inner, stI) st [])
    (hrt : Parse.rawTextList file [.ctrl name p, .group body q] = Parse.rawTextList file body.toList)
    (hW : locatedText W = locatedText inner)
    (h : Accounts file rest run stI (locatedText (flushText acc' sb' ++ W) ++ chars .unplaced "")) :
    Accounts file ([.ctrl name p, .group body q] ++ rest) run st
      (locatedText acc' ++ chars .unplaced sb') := by
  obtain ⟨newI, hdI, hkI, hvI⟩ := hI
  refine accounts_prefix file _ _ _ st stI _ _ newI h hdI ?_ ?_
  · intro s hs
    rw [hrt]
    exact hkI s hs
  · intro named hn tail
    have hv := hvI named hn
    simp only [List.nil_append] at hv
    rw [hrt]
    simp only [locatedText_append, locatedText_flushText, hW, chars_empty, List.append_nil,
      List.append_assoc]
    have := view_congr named (a := locatedText acc' ++ chars .unplaced sb') rfl
      (view_congr named hv (rfl : view named tail = view named tail))
    simpa only [List.append_assoc] using this

/-- A text-font or decoration command's arm: its argument's text, set under its font or
decoration. -/
private theorem mod_arm (K M : String → Prop) (hK : ∀ n, K n → PlainCtrl n)
    (hM : ∀ n, M n → ModCtrl n) (ctx : Ctx)
    (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String) (st : ESt)
    (hfit : Fits (fun n => K n ∨ M n) ctx) (hr : ∀ r ∈ raws, PlainRaw K M r) (hm : ModArgs M raws)
    (name : String) (p : Pos) (hi : raws[i]? = some (.ctrl name p)) (hMn : M name)
    (ih : ∀ (ctx' : Ctx) (raws' : Array Raw) (i' : Nat) (acc' : Array Inline) (sb' : String)
      (st' : ESt), sliceWeight raws' i' < sliceWeight raws i → Fits (fun n => K n ∨ M n) ctx' →
      (∀ r ∈ raws', PlainRaw K M r) → ModArgs M raws' → SpineAccounts ctx' raws' i' acc' sb' st') :
    Accounts ctx.file (raws.toList.drop i)
      ((elabInlinesFrom { ctx with callSite := none, literalWhen := none } raws i acc sb).run st) st
      (locatedText acc ++ chars .unplaced sb) := by
  have hn := hM name hMn
  obtain ⟨⟨body, q, hb⟩, htail⟩ := hm i name p hi hMn
  have h : i < raws.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hi' : raws[i] = .ctrl name p := (Array.getElem?_eq_some_iff.mp hi).2
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
  rw [dite_eq_left h]
  split
  all_goals rename_i heq
  all_goals rw [hi'] at heq
  all_goals try (cases heq; done)
  cases heq
  have F := modFacts _ hn
  have hfit' : Fits (fun n => K n ∨ M n) ({ { ctx with callSite := none, literalWhen := none }
      with macroRoles := roles } : Ctx) := hfit
  rw [find_args_none _ _ name hfit' (Or.inr hMn)]
  split
  · rename_i hu
    cases hu
  split
  · rename_i hu
    rw [lookupUser_fits _ _ name hfit' (Or.inr hMn)] at hu
    cases hu
  have haccent : raws[i + 1]?.bind (accentCompose name) = none := by
    cases raws[i + 1]? <;> simp [accentCompose, F.accent]
  have hsel : selectorHead raws (i + 1) = (none, i + 1) := by
    have hlt : i + 1 < raws.size := (Array.getElem?_eq_some_iff.mp hb).1
    have hg : raws[i + 1] = .group body q := (Array.getElem?_eq_some_iff.mp hb).2
    have hs : skipSpaces raws (i + 1) = i + 1 := by
      rw [skipSpaces]
      simp [hlt, hg]
    simp [selectorHead, hs, hb, specWord?, Compat.overlayWord?_group]
  have htail' : (if (name == "emph") = true then raws[i + 1 + 1]?.bind specWord? else none) = none := by
    by_cases he : name = "emph"
    · simp only [he, beq_self_eq_true, ↓reduceIte]
      exact htail he
    · simp [he]
  have hspec : ∀ (c : Ctx) (h : Option String) (q : Pos) (s0 : ESt), h = none →
      (selectorSpec c h q).run s0 = (none, s0) := by
    intro c h q s0 hh
    subst hh
    rfl
  have hb' : raws[(selectorHead raws (i + 1)).snd]? = some (.group body q) := by rw [hsel]; exact hb
  have hgr := hr _ (Array.mem_of_getElem? hb)
  have ⟨hbm, hbr⟩ : ModArgs M body ∧ ∀ r ∈ body, PlainRaw K M r := by
    cases hgr with
    | group _ _ hm' hr' => exact ⟨hm', hr'⟩
  have hdrop : raws.toList.drop i =
      [.ctrl name p, .group body q] ++ raws.toList.drop (i + 1 + 1) := by
    have hl : i < raws.toList.length := by simpa using h
    have hl1 : i + 1 < raws.toList.length := by
      simpa using (Array.getElem?_eq_some_iff.mp hb).1
    rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hl1]
    simp only [Array.getElem_toList, hi', (Array.getElem?_eq_some_iff.mp hb).2]
    rfl
  have hwb : sliceWeight body 0 < sliceWeight raws i := by
    have := body_lt_slice (body := body) hb (by simp only [rawWeight]; omega) (Nat.le_succ i)
    simpa [sliceWeight] using this
  have hnext2 : sliceWeight raws (i + 2) < sliceWeight raws i := sliceWeight_lt raws h (by omega)
  have hrt : Parse.rawTextList ctx.file [.ctrl name p, .group body q] =
      Parse.rawTextList ctx.file body.toList := by
    simp [Parse.rawTextList_cons, F.text]
  rcases F.kind with ⟨style, hstyle⟩ | ⟨hnone, d, hd⟩
  · simp only [F.over, F.line, F.hfill, F.qed, F.ensure, F.brk, haccent, F.esc, F.sym, F.counter,
      hstyle, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    simp only [hsel, Option.isNone_none, Bool.and_true, htail', Option.orElse_none]
    rw [run_bind']
    simp only [hspec _ none p st rfl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero]
    split
    case h_2 =>
      rename_i hw
      rw [hb'] at hw
      cases hw
    case h_3 =>
      exfalso
      rename_i h1 h2 _
      first
        | exact h1 body q hb'
        | exact h2 body q hb'
    rename_i hg
    rw [hb'] at hg
    cases hg
    rw [hdrop, fontCmdContent_plain K M hK hM body hbr,
      modifierLiteral_none_when _ _ rfl, run_bind', run_bind', modifierInlines_plain name F]
    let c0 : Ctx := { { ctx with callSite := none, literalWhen := none } with macroRoles := roles }
    let lit := (modifierLiteral c0
      (if (name == "emph" && ctx.slides) = true then Style.italic else style) none).1
    have hinner := core_plain { ctx with macroRoles := roles, literalText := lit } body st
      (fun st => ih _ body 0 #[] "" st hwb hfit hbr hbm)
    generalize (elabInlinesCore _ body).run st = R at hinner ⊢
    rcases R with ⟨inner, stI⟩
    simp only [pushModifier]
    refine arg_tail ctx.file name p q body _ _ st stI acc' inner
      (Ir.fontCmdInlines (if (name == "emph" && ctx.slides) = true then Style.italic else style)
        (if (name == "emph" && ctx.slides) = true then (false, false)
          else fontCmdEdges body.toList raws[i + 2]?) inner) sb' hinner hrt
      (locatedText_fontCmdInlines _ _ inner) ?_
    exact ih { ctx with macroRoles := roles } raws (i + 2) _ "" stI hnext2 hfit hr hm
  · simp only [F.over, F.line, F.hfill, F.qed, F.ensure, F.brk, haccent, F.esc, F.sym, F.counter,
      hnone, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    simp only [hsel]
    rw [run_bind', hspec _ none p st rfl]
    split
    case h_2 =>
      rename_i hw
      rw [hb'] at hw
      cases hw
    case h_3 =>
      exfalso
      rename_i h1 h2 _
      first
        | exact h1 body q hb'
        | exact h2 body q hb'
    rename_i hg
    rw [hb'] at hg
    cases hg
    rw [hdrop, run_bind']
    have hinner := core_plain { ctx with macroRoles := roles } body st
      (fun st => ih _ body 0 #[] "" st hwb hfit hbr hbm)
    generalize (elabInlinesCore _ body).run st = R at hinner ⊢
    rcases R with ⟨inner, stI⟩
    simp only [pushModifier]
    refine arg_tail ctx.file name p q body _ _ st stI acc' inner #[.decorated d inner] sb' hinner
      hrt rfl ?_
    exact ih { ctx with macroRoles := roles } raws (i + 2) _ "" stI hnext2 hfit hr hm

/-- One step of the spine, the steps after it lighter. -/
private theorem spine_step (K M : String → Prop) (hK : ∀ n, K n → PlainCtrl n)
    (hM : ∀ n, M n → ModCtrl n) (ctx : Ctx)
    (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String) (st : ESt)
    (hfit : Fits (fun n => K n ∨ M n) ctx) (hr : ∀ r ∈ raws, PlainRaw K M r) (hm : ModArgs M raws)
    (ih : ∀ (ctx' : Ctx) (raws' : Array Raw) (i' : Nat) (acc' : Array Inline) (sb' : String)
      (st' : ESt), sliceWeight raws' i' < sliceWeight raws i → Fits (fun n => K n ∨ M n) ctx' →
      (∀ r ∈ raws', PlainRaw K M r) → ModArgs M raws' → SpineAccounts ctx' raws' i' acc' sb' st') :
    Accounts ctx.file (raws.toList.drop i)
      ((elabInlinesFrom { ctx with callSite := none, literalWhen := none } raws i acc sb).run st) st
      (locatedText acc ++ chars .unplaced sb) := by
  by_cases hmod : ∃ name p, raws[i]? = some (.ctrl name p) ∧ M name
  · obtain ⟨name, p, hi, hMn⟩ := hmod
    exact mod_arm K M hK hM ctx raws i acc sb st hfit hr hm name p hi hMn ih
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
        (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr hm)
        (by simp) (by simp) ?_
      intro named _ tail
      simp only [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
        locatedOne_located, locatedOne_text, locatedList_cons, locatedList_nil,
        Parse.rawTextOne_word, Option.map_none, Option.getD_none, List.append_nil,
        List.append_assoc, chars_empty]
      rw [← List.append_assoc (locatedText acc'), ← List.append_assoc (locatedText acc')]
      exact view_token named _ (wordAfter_canon _ _ _ _) _ _
    case h_2.space =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) acc' _ st hnext hfit hr hm)
        (by simp) (by simp) ?_
      intro named _ tail
      simp only [Parse.rawTextOne_space]
      exact view_pending_space named _ sb' tail
    case h_3.par p =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) acc' _ st hnext hfit hr hm)
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
      have hfit' : Fits (fun n => K n ∨ M n) ({ { ctx with callSite := none, literalWhen := none }
          with macroRoles := roles } : Ctx) := hfit
      rw [find_args_none _ _ name hfit' (Or.inl hk)]
      split
      · rename_i hu
        cases hu
      split
      · rename_i hu
        rw [lookupUser_fits _ _ name hfit' (Or.inl hk)] at hu
        cases hu
      obtain ⟨hover, hacc, hcase⟩ := hK name hk
      simp only [hover]
      by_cases hhf : name = "hfill"
      · subst hhf
        simp only [show ("hfill" == "hfill") = true by decide, ↓reduceIte]
        refine accounts_cons ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr hm)
          (by simp) (by simp) ?_
        intro named _ tail
        simp [locatedText_push, locatedText_flushText, locatedOne, locatedOnto, Parse.ctrlText,
          hover]
      by_cases hpar : name = "par"
      · subst hpar
        simp only [show ("par" == "hfill") = false by decide, show ("par" == "qedhere") = false by decide,
          show ("par" == "ensuremath") = false by decide,
          show ("par" == "\\") = false by decide, beq_self_eq_true, Bool.or_true,
          Bool.false_eq_true, ↓reduceIte]
        obtain ⟨k, hk'⟩ := drop_skipSpaces raws (i + 1)
        rw [hk', ← List.cons_append]
        have hj := Parse.skipSpaces_ge raws (i + 1)
        refine accounts_prefix ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (skipSpaces raws (i + 1)) _ "" st
            (sliceWeight_lt raws h (by omega)) hfit hr hm) (by simp) (by simp) ?_
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
      simp only [unspelled_not_lineCtrl name hown n1 n2, beq_eq_false_iff_ne.mpr hhf,
        beq_eq_false_iff_ne.mpr n3, beq_eq_false_iff_ne.mpr n4,
        beq_eq_false_iff_ne.mpr n5, beq_eq_false_iff_ne.mpr hpar, haccent, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte]
      cases hesc : escapeOf name with
      | some lit =>
        simp only []
        by_cases hsp : name = " "
        · subst hsp
          have hlit : lit = " " := by
            rw [escapeOf_space, Option.some.injEq] at hesc
            exact hesc.symm
          subst hlit
          simp only [beq_self_eq_true, ↓reduceIte]
          refine accounts_cons ctx.file _ _ _ st st _ _ []
            (ih { ctx with macroRoles := roles } raws (i + 1) acc' _ st hnext hfit hr hm)
            (by simp) (by simp) ?_
          intro named _ tail
          simp [Parse.ctrlText, hover, chars]
        · simp only [beq_eq_false_iff_ne.mpr hsp, Bool.false_eq_true, ↓reduceIte]
          refine accounts_cons ctx.file _ _ _ st st _ _ []
            (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr hm)
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
          rw [escapeOf_space] at hesc
          cases hesc
        simp only [ht, Option.getD_some]
        refine accounts_cons ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr hm)
          (by simp) (by simp) ?_
        intro named _ tail
        simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
          locatedList_cons, Parse.ctrlText, hover, hesc, hhf, hpar, n5, hsp', ht]
    case h_12.mod name p hMn =>
      exact absurd ⟨name, p, by rw [Array.getElem?_eq_getElem h, heq], hMn⟩ hmod
    case h_4.sym p | h_5.sym p | h_6.sym p =>
      refine accounts_cons ctx.file _ _ _ st st _ _ []
        (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr hm)
        (by simp) (by simp) ?_
      intro named _ tail
      simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
        locatedList_cons, chars]
    case h_7.sym c p h1 h2 h3 =>
      have hc : c ≠ '~' := h3
      split
      · refine accounts_cons ctx.file _ _ _ st st _ _ []
          (ih { ctx with macroRoles := roles } raws (i + 1) _ "" st hnext hfit hr hm)
          (by simp) (by simp) ?_
        intro named _ tail
        simp [locatedText_push, locatedText_flushText, sourceInline, Ctx.sourceSpan,
          locatedList_cons, chars, hc]
      · refine accounts_cons ctx.file _ _ _ st _ _ _ [⟨ctx.file, p⟩]
          (ih { ctx with macroRoles := roles } raws (i + 1) acc' sb' _ hnext hfit hr hm) ?_ ?_ ?_
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
    case h_9.group body p _ _ =>
      have hb : ∀ r ∈ body, PlainRaw K M r := by assumption
      have hbm : ModArgs M body := by assumption
      rw [run_group]
      refine accounts_inner ctx.file ctx.file _ body _ _ st _ _ _ _
        (core_plain { ctx with macroRoles := roles } body st fun st =>
          ih { ctx with macroRoles := roles.enter } body 0 #[] "" st (hgroup heq) hfit hb hbm)
        (by simp) rfl ?_
      rw [← pre_inner]
      exact ih { ctx with macroRoles := roles } raws (i + 1) _ "" _ hnext hfit hr hm
    case h_10.scope body p _ _ =>
      have hb : ∀ r ∈ body, PlainRaw K M r := by assumption
      have hbm : ModArgs M body := by assumption
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [run_bind']
      refine accounts_inner ctx.file ctx.file _ body _ _ st _ _ _ _
        (core_plain { ctx with macroRoles := roles } body st fun st =>
          ih { ctx with macroRoles := roles.enter } body 0 #[] "" st (henv heq) hfit hb hbm)
        (by simp [inputEnvFile?_scope]) rfl ?_
      rw [← pre_inner]
      exact ih { ctx with macroRoles := roles } raws (i + 1) _ "" _ hnext hfit hr hm
    case h_10.input name body p f _ _ _ =>
      have hb : ∀ r ∈ body, PlainRaw K M r := by assumption
      have hbm : ModArgs M body := by assumption
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
          ih { ictx with macroRoles := roles.enter } body 0 #[] "" st (henv heq) hfit hb hbm)
        (by simp [hf]) rfl ?_
      rw [← pre_inner]
      exact ih { ctx with macroRoles := roles } raws (i + 1) _ "" _ hnext hfit hr hm
  · simp only [h, ↓reduceDIte]
    have hdrop : raws.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using Nat.not_lt.mp h)
    rw [hdrop]
    refine ⟨[], by rw [List.append_nil]; rfl, by simp, fun named _ => ?_⟩
    show view named (locatedText (mergeTexts (flushText acc' sb'))) = _
    rw [locatedText_mergeTexts, locatedText_flushText]
    simp

private theorem spine_plain (K M : String → Prop) (hK : ∀ n, K n → PlainCtrl n)
    (hM : ∀ n, M n → ModCtrl n) (ctx : Ctx)
    (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String) (st : ESt)
    (hfit : Fits (fun n => K n ∨ M n) ctx) (hr : ∀ r ∈ raws, PlainRaw K M r) (hm : ModArgs M raws) :
    SpineAccounts ctx raws i acc sb st := by
  have key : ∀ n (ctx : Ctx) (raws : Array Raw) (i : Nat) (acc : Array Inline) (sb : String)
      (st : ESt), sliceWeight raws i = n → Fits (fun n => K n ∨ M n) ctx →
      (∀ r ∈ raws, PlainRaw K M r) → ModArgs M raws → SpineAccounts ctx raws i acc sb st := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ctx raws i acc sb st hn hfit hr hm
      exact spine_step K M hK hM ctx raws i acc sb st hfit hr hm
        fun ctx' raws' i' acc' sb' st' hlt hfit' hr' hm' =>
          ih _ (hn ▸ hlt) ctx' raws' i' acc' sb' st' rfl hfit' hr' hm'
  exact key _ ctx raws i acc sb st rfl hfit hr hm

/-- The plain-text arms of the inline knot conserve the source's text: once the reserved
characters it refuses are excused, a run of words, spaces, breaks and symbols, through groups,
declaration scopes and input wrappers, reads as its source. -/
public theorem elabInlines_plain_text (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (hsite : ctx.callSite = none) (hwhen : ctx.literalWhen = none)
    (hr : ∀ r ∈ raws, PlainRaw (fun _ => False) (fun _ => False) r) :
    Accounts ctx.file raws.toList ((elabInlines ctx raws).run st) st [] := by
  rw [elabInlines]
  exact core_enter ctx raws st hsite hwhen fun st =>
    spine_plain _ _ (fun _ h => h.elim) (fun _ h => h.elim)
      { ctx with macroRoles := ctx.macroRoles.enter } raws 0 #[] "" st
      ⟨fun _ _ h => h.elim (·) (·), fun _ _ h => h.elim (·) (·)⟩ hr (fun _ _ _ _ h => h.elim)

/-- Control words that set their own text conserve it too: with no parameter or document command
taking their names, `\hfill`, `\par`, and escapes and text symbols no accent shares read as their
source among the plain-text arms. -/
public theorem elabInlines_ctrl_text (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (hsite : ctx.callSite = none) (hwhen : ctx.literalWhen = none) (hfit : Fits PlainCtrl ctx)
    (hr : ∀ r ∈ raws, PlainRaw PlainCtrl (fun _ => False) r) :
    Accounts ctx.file raws.toList ((elabInlines ctx raws).run st) st [] := by
  rw [elabInlines]
  exact core_enter ctx raws st hsite hwhen fun st =>
    spine_plain _ _ (fun _ h => h) (fun _ h => h.elim)
      { ctx with macroRoles := ctx.macroRoles.enter } raws 0 #[] "" st
      ⟨fun a ha h => h.elim (hfit.1 a ha) (·), fun c hc h => h.elim (hfit.2 c hc) (·)⟩ hr
      (fun _ _ _ _ h => h.elim)

/-- The text-font and decoration commands conserve their argument's text: `\textbf{…}`, `\emph{…}`,
`\underline{…}` and the like, each directly before its braced argument and `\emph` before no overlay
word, read as that argument among the plain-text arms and the control words setting their own text. -/
public theorem elabInlines_modifier_text (ctx : Ctx) (raws : Array Raw) (st : ESt)
    (hsite : ctx.callSite = none) (hwhen : ctx.literalWhen = none)
    (hfit : Fits (fun n => PlainCtrl n ∨ ModCtrl n) ctx)
    (hr : ∀ r ∈ raws, PlainRaw PlainCtrl ModCtrl r) (hm : ModArgs ModCtrl raws) :
    Accounts ctx.file raws.toList ((elabInlines ctx raws).run st) st [] := by
  rw [elabInlines]
  exact core_enter ctx raws st hsite hwhen fun st =>
    spine_plain _ _ (fun _ h => h) (fun _ h => h)
      { ctx with macroRoles := ctx.macroRoles.enter } raws 0 #[] "" st hfit hr hm

end LeanTex.Core.Elab
