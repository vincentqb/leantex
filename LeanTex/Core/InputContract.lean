module

public import LeanTex.Core.CompatContract
public import LeanTex.Core.Elab
public import LeanTex.Core.Surface
public import LeanTex.Core.MdDesugarContract

import all LeanTex.Core.Elab
import all LeanTex.Core.Compat
import all LeanTex.Core.Parse

namespace LeanTex.Core.CompatContract

public theorem inputRequest_names_asked (request : Compat.InputRequest) :
    (request.command = "usepackage" ∨ request.command = "RequirePackage" →
      ∀ part ∈ request.name.splitOn ",",
        part.trimAscii.toString.isEmpty = false →
        Compat.nativePackages.contains part.trimAscii.toString = false →
        (Compat.localStyCandidates request.call).contains
          part.trimAscii.toString = true) ∧
    (∀ row ∈ Compat.themeAsking, request.command = row.1 →
      request.name.trimAscii.toString.isEmpty = false →
      (Compat.localStyCandidates request.call).contains
        (row.2 ++ request.name.trimAscii.toString) = true) := by
  constructor
  · intro hcommand part hpart hnonempty hnative
    exact (nameRefusals_asked request.callPos request.operands).1
      request.command hcommand part hpart hnonempty hnative
  · intro row hrow hcommand hnonempty
    cases request with
    | mk command file pos callPos operands =>
      simp only at hcommand
      subst command
      exact (nameRefusals_asked callPos operands).2 row hrow hnonempty

end LeanTex.Core.CompatContract

namespace LeanTex.Core.Elab

/-- The producer's whole diagnostic record survives in `ds`, at most its site
count moved to its carrier. -/
@[expose] public def Reported (ds : Array Diag) (producer : Diag) : Prop :=
  ∃ actual ∈ ds, { actual with sites := producer.sites } = producer

public theorem reported_of_mem (ds : Array Diag) (d : Diag) (h : d ∈ ds) :
    Reported ds d :=
  ⟨d, h, rfl⟩

public theorem reported_tally (ds : Array Diag) (d : Diag) (h : Reported ds d) :
    Reported (Diag.tallySites ds) d := by
  obtain ⟨before, hb, heq⟩ := h
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hb
  have ht := Diag.tallySites_record_exact ds i hi
  cases helem : (Diag.tallySites ds)[i]? with
  | none => simp only [helem, Option.map_none] at ht; contradiction
  | some actual =>
    simp only [helem, Option.map_some, Option.some.injEq] at ht
    refine ⟨actual, Array.mem_iff_getElem?.mpr ⟨i, helem⟩, ?_⟩
    rw [hget] at ht
    have := congrArg (fun report : Diag => { report with sites := d.sites }) ht
    exact this.trans heq

public theorem reported_append (left right : Array Diag) (d : Diag) (h : Reported left d) :
    Reported (left ++ right) d := by
  obtain ⟨actual, ha, heq⟩ := h
  exact ⟨actual, Array.mem_append.mpr (Or.inl ha), heq⟩

public theorem completePrepared_reports_contract (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) (d : Diag)
    (h : d ∈ earlier ++ p.compatDiags) :
    Reported (completePrepared file p earlier doc table report st).2.1
      (p.sourceTriggers.attribute d) := by
  unfold completePrepared
  dsimp only
  apply reported_tally
  apply reported_of_mem
  refine Array.mem_map.mpr ⟨d, ?_, rfl⟩
  apply accountRecovered_mem
  exact Array.mem_append.mpr (Or.inl
    (Array.mem_append.mpr (Or.inl
      (Array.mem_append.mpr (Or.inl
        (Array.mem_append.mpr (Or.inl
          (Array.mem_append.mpr (Or.inl
            (Array.mem_append.mpr (Or.inl
              (Array.mem_append.mpr (Or.inl
                (Array.mem_append.mpr (Or.inl
                  (Array.mem_append.mpr (Or.inl h)))))))))))))))))

public theorem runPrepared_reports_contract (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (withdrawn : Array String)
    (d : Diag) (h : d ∈ earlier ++ p.compatDiags) :
    Reported (runPrepared file p earlier metric withdrawn).2.1
      (p.sourceTriggers.attribute d) := by
  obtain ⟨doc, table, report, st, heq⟩ :=
    runPrepared_complete_exact file p earlier metric withdrawn
  rw [heq]
  exact completePrepared_reports_contract file p earlier doc table report st d h

attribute [local irreducible] runPrepared

public theorem runPreparedFinal_reports_contract (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (d : Diag)
    (h : d ∈ earlier ++ p.compatDiags) :
    Reported (runPreparedFinal file p earlier metric).2 (p.sourceTriggers.attribute d) := by
  unfold runPreparedFinal finishPreparedRuns
  dsimp only
  split
  · exact reported_tally _ _ (reported_append _ _ _
      (runPrepared_reports_contract file p earlier metric #[] d h))
  · exact reported_tally _ _ (reported_append _ _ _
      (runPrepared_reports_contract file p earlier metric _ d h))

attribute [local irreducible] Compat.rewriteText in
public theorem prepareRewritten_diags_covers (file : String)
    (scan : Compat.BoundaryScan) (macros : Array (String × String))
    (triggers : Compat.SourceTriggers) (prior : Array Diag)
    (rewritten : Array Parse.Raw × Array Diag × Array String)
    (attempts : Array Compat.InputAttempt) (mentions : Array String) (d : Diag)
    (h : d ∈ rewritten.2.1) :
    d ∈ (prepareRewritten file scan macros triggers prior rewritten attempts mentions).compatDiags := by
  rcases rewritten with ⟨raws, diags, warned⟩
  unfold prepareRewritten
  cases Compat.rewriteText file raws warned
  exact Array.mem_append.mpr (Or.inl (Array.mem_append.mpr (Or.inr h)))

attribute [local irreducible] prepareRewritten Compat.rewriteExecuted
  Compat.boundaryScan macroScan in
public theorem prepareExecuted_diags_covers (file : String)
    (executed : Compat.Executed) (d : Diag)
    (h : d ∈ (Compat.rewriteExecuted executed).2.1) :
    d ∈ (prepareExecuted file executed).compatDiags :=
  prepareRewritten_diags_covers file _ _ _ _ _ _ _ d h

attribute [local irreducible] prepareExecuted runPreparedFinal in
public theorem runExecuted_reports_contract (file : String)
    (executed : Compat.Executed) (earlier : Array Diag)
    (metric : Ir.Pic.LabelMetric) (d : Diag)
    (h : d ∈ (Compat.rewriteExecuted executed).2.1) :
    Reported (runExecuted file executed earlier metric).2
      (executed.sourceTriggers.attribute d) := by
  simpa only [runExecuted, prepareExecuted_sourceTriggers_exact] using
    runPreparedFinal_reports_contract file (prepareExecuted file executed) earlier metric d
      (Array.mem_append.mpr (Or.inr (prepareExecuted_diags_covers file executed d h)))

attribute [local irreducible] executeInputs Compat.executeInputs
  Compat.rewriteExecuted runExecuted in
public theorem packageInput_refusal_contract (reader : Compat.InputReader Id)
    (file command names : String) (pos groupPos namePos : Pos)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hnames : Compat.ExternalPackageNames names)
    (hr : ∀ request context, reader request context = (none, context)) :
    let executed := executeInputs reader file
      (Compat.packageCall command names pos groupPos namePos)
    let request : Compat.InputRequest :=
      ⟨command, file, pos, pos, #[.group #[.word names namePos] groupPos]⟩
    executed.inputAttempts = #[⟨request, false⟩] ∧
      ∀ part ∈ names.trimAscii.toString.splitOn ",",
        (Compat.localStyCandidates request.call).contains part.trimAscii.toString = true ∧
        Reported (runExecuted file executed earlier metric).2
          (executed.sourceTriggers.attribute
            (Compat.packageRefusal file pos part.trimAscii.toString)) := by
  let request : Compat.InputRequest :=
    ⟨command, file, pos, pos, #[.group #[.word names namePos] groupPos]⟩
  have hproducer :
      let executed := executeInputs reader file
        (Compat.packageCall command names pos groupPos namePos)
      executed.inputAttempts = #[⟨request, false⟩] ∧
        ∀ part ∈ names.trimAscii.toString.splitOn ",",
          executed.sourceTriggers.attribute
            (Compat.packageRefusal file pos part.trimAscii.toString) ∈
              (Compat.rewriteExecuted executed).2.1 := by
    unfold executeInputs
    rw [settleSplits_package_exact file command names pos groupPos namePos]
    exact Compat.executeInputs_package_refusal_contract reader file command names
      pos groupPos namePos _ #[] _ hc (by rcases hc with rfl | rfl <;> decide +kernel) hnames hr
  refine ⟨hproducer.1, ?_⟩
  intro part hpart
  have hname : request.name = names.trimAscii.toString :=
    Compat.InputRequest.package_name_exact file command names pos groupPos namePos
  constructor
  · exact (CompatContract.inputRequest_names_asked request).1 hc part
      (by simpa only [hname] using hpart) (hnames part hpart).1 (hnames part hpart).2.1
  · simpa only [Compat.SourceTriggers.attribute_fixed_point] using
      runExecuted_reports_contract file _ earlier metric _ (hproducer.2 part hpart)

open Parse Ir

private theorem inputEnvFile?_inputEnv (f : String) :
    Parse.inputEnvFile? (Parse.inputEnv f) = some f := by
  have hs : ("input " ++ f).startsWith "input " = true := by
    simp [String.toList_append]
  simp only [Parse.inputEnvFile?, Parse.inputEnv, hs, ite_true, Option.some.injEq]
  apply String.ext
  simp [String.toList_append, show "input ".length = 6 by decide]

private theorem inputEnv_ne_scopeEnv (f : String) : Parse.inputEnv f ≠ Parse.scopeEnv := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [Parse.inputEnv, Parse.scopeEnv] at this

private theorem inputEnv_ne_linkedBoxRowMark (f : String) :
    Parse.inputEnv f ≠ Compat.linkedBoxRowMark := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [Parse.inputEnv, Compat.linkedBoxRowMark] at this

private theorem inputEnv_ne_tikzpicture (f : String) :
    (Parse.inputEnv f != "tikzpicture") = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [Parse.inputEnv] at this

private theorem inputEnv_ne_tikzcd (f : String) :
    (Parse.inputEnv f != "tikzcd") = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [Parse.inputEnv] at this

private theorem pictureInSentence_input (ctx : Ctx) (f : String) (cur raws : Array Raw) (i : Nat)
    (pos : Pos) : pictureInSentence ctx (Parse.inputEnv f) cur raws i pos = pure () := by
  simp [pictureInSentence, inputEnv_ne_tikzpicture, inputEnv_ne_tikzcd]

private theorem openLengthScope_inert (ctx : Ctx) (raws : Array Raw)
    (h : lengthScopeKeys? raws = none) :
    openLengthScope ctx raws = (#[], ⟨raws, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩) := by
  simp [openLengthScope, h]

private theorem lengthScopeKeys?_back (body : Array Raw)
    (h : ∀ n p, body.back? = some (.ctrl n p) → Compat.lengthRestoreKeys? n = none) :
    lengthScopeKeys? body = none := by
  unfold lengthScopeKeys?
  split
  · next n p heq => exact h n p heq
  · rfl

/-- Whether a raw is blank source between blocks: a space,
or a paragraph break the source wrote. -/
@[expose] public def sourceBlank : Raw → Bool
  | .space => true
  | .par p => p.origins.isEmpty
  | _ => false

private theorem flowCtx_macroRoles (ctx : Ctx) (st : ESt) (gen : Nat) :
    (flowCtx ctx st gen).macroRoles = ctx.macroRoles := by
  unfold flowCtx
  split <;> rfl

private theorem flowCtx_idle (ctx : Ctx) (st : ESt) : flowCtx ctx st st.flowGen = ctx := by
  simp [flowCtx]

private theorem withRoles_default (c : Ctx)
    (hc : c.macroRoles = ({file := ""} : Ctx).macroRoles) :
    { c with macroRoles := {} } = c := by
  cases c
  cases hc
  rfl

private theorem blockMacroStep_quiet (ctx : Ctx) (st : ESt) (gen : Nat) (raws : Array Raw)
    (i : Nat) (blocks : Array Block) (cur : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hi : i < raws.size) (hp : (raws[i]).origins? = some [] ∨ (raws[i]).origins? = none) :
    blockMacroStep ctx st gen raws i blocks cur =
      pure (flowMCtx ctx st gen, blocks, cur) := by
  have hf := flowCtx_macroRoles ctx st gen
  rw [hm] at hf
  rcases hp with hp | hp
  · simp only [blockMacroStep, flowMCtx, blockMacroKinds, Array.getElem?_eq_getElem hi, hp, hf,
      MacroRoles.empty]
    simp [relativeOrigins, show ¬ i ≥ raws.size by omega,
      closeBlockFrameSources, commonOrigins, moveMacroRuns, closeMacroRuns, hf, MacroRoles.empty]
    congr 2
    exact Subtype.ext (withRoles_default _ hf)
  · simp only [blockMacroStep, flowMCtx, blockMacroKinds, Array.getElem?_eq_getElem hi, hp, hf,
      MacroRoles.empty]
    simp [show ¬ i ≥ raws.size by omega,
      closeBlockFrameSources, commonOrigins, moveMacroRuns, closeMacroRuns, hf, MacroRoles.empty]
    congr 2
    exact Subtype.ext (withRoles_default _ hf)

private theorem sourceBlank_origins (r : Raw) (h : sourceBlank r = true) :
    r.origins? = some [] ∨ r.origins? = none := by
  cases r <;> simp_all [sourceBlank, Raw.origins?]

private theorem sourceBlank_spaceOrPar (r : Raw) (h : sourceBlank r = true) :
    isSpaceOrPar r = true := by
  cases r <;> simp_all [sourceBlank, isSpaceOrPar]

private theorem sourceBlank_of_mem (xs : Array Raw) (h : xs.all sourceBlank = true) (r : Raw)
    (hr : r ∈ xs) : sourceBlank r = true :=
  Array.all_eq_true_iff_forall_mem.mp h r hr

private theorem elabBlocksGo_blank (ctx : Ctx) (st : ESt) (raws : Array Raw) (i gen : Nat)
    (blocks : Array Block) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hi : i < raws.size) (hb : sourceBlank raws[i] = true) :
    (elabBlocksGo ctx raws i blocks #[] gen).run st =
      (elabBlocksGo (flowCtx ctx st gen) raws (i + 1) blocks #[] st.flowGen).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_quiet ctx st gen raws i blocks #[] hm hi (sourceBlank_origins _ hb)]
  simp only [pure_bind, flowMCtx, hi, dite_true]
  have hfm : (flowCtx ctx st gen).macroRoles = ({file := ""} : Ctx).macroRoles := by
    rw [flowCtx_macroRoles]; exact hm
  split
  · rename_i heq; rw [heq] at hb; simp [sourceBlank] at hb
  · rw [flushPara_empty _ blocks hfm]; rfl
  · rename_i heq; rw [heq] at hb; simp [sourceBlank] at hb
  · rename_i heq; rw [heq] at hb; simp [sourceBlank] at hb
  · rename_i heq; rw [heq] at hb; simp [sourceBlank] at hb
  · rename_i heq; rw [heq] at hb; simp [sourceBlank] at hb
  · simp [sourceBlank_spaceOrPar _ hb]

private theorem elabBlocksGo_input_at (ctx : Ctx) (st : ESt) (raws : Array Raw) (i : Nat)
    (f : String) (body : Array Raw) (pos : Pos) (gen : Nat) (hg : st.flowGen = gen)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hb : bodyIsBlock body = true) (hi : i < raws.size)
    (hr : raws[i] = .env (Parse.inputEnv f) body pos) :
    (elabBlocksGo ctx raws i #[] #[] gen).run st =
      ((do
        let bs ← elabEnvArm ctx (Parse.inputEnv f) body pos #[]
        elabBlocksGo ctx raws (i + 1)
          (Ir.markDisplay false (parFollows raws (i + 1)) false 0 bs) #[] gen) :
        EM (Array Block)).run st := by
  subst hg
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st raws i #[] #[] hm hi (by rw [hr]; simpa [Raw.origins?] using hp)]
  simp only [pure_bind, hi, dite_true]
  split
  · rename_i heq; rw [hr] at heq; cases heq
  · rename_i heq; rw [hr] at heq; cases heq
  · rename_i heq; rw [hr] at heq; cases heq
  · rename_i heq; rw [hr] at heq; cases heq
  · rename_i heq
    rw [hr] at heq
    cases heq
    simp [inputEnv_ne_linkedBoxRowMark, inputEnvFile?_inputEnv, hb, pictureInSentence_input,
      flushPara_empty ctx _ hm, Ir.flushedText_empty_exact, Ir.lastLeavesEndPe_empty_exact,
      Ir.markInParagraph_false_id, endPeAt, envGroup]
  · rename_i heq; rw [hr] at heq; cases heq
  · rename_i _ _ _ _ henv _
    exact absurd hr (henv _ _ _)

private theorem elabEnvArm_input_scope (ctx : Ctx) (f : String) (body : Array Raw) (pos : Pos)
    (hlen : lengthScopeKeys? body = none) :
    elabEnvArm ctx (Parse.inputEnv f) body pos #[] =
      splicedFrameScope (some 0) (elabBlockScope { ctx with file := f, callSite := none } body) := by
  rw [elabEnvArm, openLengthScope_inert ctx body hlen]
  simp [inputEnv_ne_scopeEnv, inputEnvFile?_inputEnv, closeLengthScope]
  rfl

private theorem elabBlocksGo_blanks_end (raws : Array Raw) (blocks : Array Block) :
    ∀ (n i gen : Nat) (ctx : Ctx) (st : ESt), raws.size - i = n →
      ctx.macroRoles = ({file := ""} : Ctx).macroRoles →
      (∀ j (hj : j < raws.size), i ≤ j → sourceBlank raws[j] = true) →
      (elabBlocksGo ctx raws i blocks #[] gen).run st = (blocks, st)
  | 0, i, gen, ctx, st, hn, hm, _ => elabBlocksGo_end ctx st raws i blocks gen hm (by omega)
  | n + 1, i, gen, ctx, st, hn, hm, hb => by
    have hi : i < raws.size := by omega
    rw [elabBlocksGo_blank ctx st raws i gen blocks hm hi (hb i hi (Nat.le_refl i))]
    exact elabBlocksGo_blanks_end raws blocks n (i + 1) st.flowGen _ st (by omega)
      (by rw [flowCtx_macroRoles]; exact hm) (fun j hj hij => hb j hj (by omega))

private theorem elabBlocksGo_blanks_skip (ctx : Ctx) (raws : Array Raw) (blocks : Array Block)
    (k gen : Nat) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hk : k ≤ raws.size) :
    ∀ (n i : Nat) (st : ESt), st.flowGen = gen → k - i = n → i ≤ k →
      (∀ j (hj : j < raws.size), i ≤ j → j < k → sourceBlank raws[j] = true) →
      (elabBlocksGo ctx raws i blocks #[] gen).run st =
        (elabBlocksGo ctx raws k blocks #[] gen).run st
  | 0, i, st, _, hn, hik, _ => by rw [show i = k by omega]
  | n + 1, i, st, hg, hn, hik, hb => by
    have hi : i < raws.size := by omega
    subst hg
    rw [elabBlocksGo_blank ctx st raws i st.flowGen blocks hm hi
      (hb i hi (Nat.le_refl i) (by omega)), flowCtx_idle]
    exact elabBlocksGo_blanks_skip ctx raws blocks k st.flowGen hm hk n (i + 1) st rfl (by omega)
      (by omega) (fun j hj h1 h2 => hb j hj (by omega) h2)

private theorem parFollows_include (pre post : Array Raw) (w : Raw)
    (hpost : post.all sourceBlank = true) :
    parFollows (pre ++ #[w] ++ post) (pre.size + 1) = post.any (· matches .par _) := by
  have hx : ((pre ++ #[w] ++ post).extract (pre.size + 1) (pre ++ #[w] ++ post).size).toList =
      post.toList := by
    simp [List.drop_append]
  have hb : ∀ r ∈ post.toList, sourceBlank r = true := fun r hr =>
    sourceBlank_of_mem post hpost r (Array.mem_toList_iff.mp hr)
  unfold parFollows
  rw [hx, ← Array.any_toList]
  generalize post.toList = l at hb ⊢
  induction l with
  | nil => rfl
  | cons r rest ih =>
    cases r with
    | space =>
      simp only [List.dropWhile_cons, ↓reduceIte, List.any_cons]
      simpa using ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    | par p => simp
    | _ => simp [sourceBlank] at hb

private theorem lengthScopeKeys?_include (pre post : Array Raw) (f : String) (body : Array Raw)
    (pos : Pos) (hpost : post.all sourceBlank = true) :
    lengthScopeKeys? (pre ++ #[.env (Parse.inputEnv f) body pos] ++ post) = none := by
  apply lengthScopeKeys?_back
  intro n p h
  rw [Array.back?_append] at h
  cases hb : post.back? with
  | none => simp [hb] at h
  | some r =>
    rw [hb] at h
    simp only [Option.some_or, Option.some.injEq] at h
    subst h
    have := sourceBlank_of_mem post hpost _ (Array.mem_of_back? hb)
    simp [sourceBlank] at this

private theorem closeBlockScope_base (ctx : Ctx) (base : Option Nat) (blocks : Array Block)
    (st : ESt) :
    (closeBlockScope ctx #[] base blocks).run st =
      (blocks, { st with spans := { st.spans with frames := { st.spans.frames with base } } }) := by
  simp [closeBlockScope, closeLengthScope, setFrameSourceBase]
  rfl

/-- A block accumulator's entry state: its scheduled splice
offset becomes its base. -/
private def openScope (st : ESt) : ESt :=
  { st with spans := { st.spans with frames :=
    { st.spans.frames with base := st.spans.frames.nextBase, nextBase := none } } }

private theorem elabBlockScope_run (ctx : Ctx) (st : ESt) (raws : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hlen : openLengthScope ctx raws =
      (#[], ⟨raws, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)) :
    (elabBlockScope ctx raws).run st =
      ((do
        let bs ← elabBlocksGo ctx raws 0 #[] #[] st.flowGen
        closeBlockScope ctx #[] st.spans.frames.base bs) :
        EM (Array Block)).run (openScope st) := by
  have henter : {ctx with macroRoles := ctx.macroRoles.enter} = ctx := by
    cases ctx
    cases hm
    rfl
  rw [elabBlockScope]
  simp only [henter, openBlockScope, hlen, bind_assoc, pure_bind]
  rfl

private theorem splicedFrameScope_zero (scope : EM (Array Block)) (st : ESt) :
    (splicedFrameScope (some 0) scope).run st =
      scope.run { st with spans := { st.spans with frames :=
        { st.spans.frames with nextBase := st.spans.frames.base } } } := by
  cases hb : st.spans.frames.base <;>
    simp [splicedFrameScope, FrameSources.offset, hb]

private theorem elabBlocks_run (ctx : Ctx) (raws : Array Raw) (st : ESt) :
    (elabBlocks ctx raws).run st =
      (elabBlockScope ctx raws).run { st with spans := { st.spans with frames :=
        { st.spans.frames with nextBase := some 0 } } } := rfl

/-- The dispatch domain where a wrapped file splices: no macro expansion open, a
positioned wrapper, block-shaped raws. -/
@[expose] public def InputSplice (ctx : Ctx) (body : Array Raw) (pos : Pos) : Prop :=
  ctx.macroRoles = ({file := ""} : Ctx).macroRoles ∧ pos.origins = [] ∧ bodyIsBlock body = true ∧
    ∀ n p, body.back? = some (.ctrl n p) → Compat.lengthRestoreKeys? n = none

private theorem elabBlockScope_input_exact (ctx : Ctx) (f : String) (body pre post : Array Raw)
    (pos : Pos) (st : ESt) (h : InputSplice ctx body pos)
    (hpre : pre.all sourceBlank = true) (hpost : post.all sourceBlank = true) :
    (elabBlockScope ctx (pre ++ #[.env (Parse.inputEnv f) body pos] ++ post)).run st =
      let r := (elabBlockScope { ctx with file := f, callSite := none } body).run st
      (Ir.markDisplay false (post.any (· matches .par _)) false 0 r.1, r.2) := by
  obtain ⟨hm, hp, hb, hl⟩ := h
  have hlen := lengthScopeKeys?_back body hl
  have hmF : ({ ctx with file := f, callSite := none } : Ctx).macroRoles =
      ({file := ""} : Ctx).macroRoles := hm
  have hsize : (pre ++ #[Raw.env (Parse.inputEnv f) body pos] ++ post).size =
      pre.size + 1 + post.size := by simp
  have hw : (pre ++ #[Raw.env (Parse.inputEnv f) body pos] ++ post)[pre.size]'(by omega) =
      .env (Parse.inputEnv f) body pos := by
    simp [Array.getElem_append_left]
  have hblank : ∀ j (hj : j < (pre ++ #[Raw.env (Parse.inputEnv f) body pos] ++ post).size),
      j ≠ pre.size →
        sourceBlank (pre ++ #[Raw.env (Parse.inputEnv f) body pos] ++ post)[j] = true := by
    intro j hj hne
    by_cases hlt : j < pre.size
    · rw [Array.getElem_append_left (by simp; omega), Array.getElem_append_left hlt]
      exact sourceBlank_of_mem pre hpre _ (Array.getElem_mem hlt)
    · rw [Array.getElem_append_right (by simp; omega)]
      exact sourceBlank_of_mem post hpost _ (Array.getElem_mem _)
  rw [elabBlockScope_run ctx st _ hm (openLengthScope_inert _ _
      (lengthScopeKeys?_include pre post f body pos hpost)),
    elabBlockScope_run _ st body hmF (openLengthScope_inert _ _ hlen)]
  simp only [StateT.run_bind]
  rw [elabBlocksGo_blanks_skip ctx _ #[] pre.size st.flowGen hm (by omega) pre.size 0
      (openScope st) rfl (by omega) (by omega) (fun j hj _ hjk => hblank j hj (by omega)),
    elabBlocksGo_input_at ctx (openScope st) _ pre.size f body pos st.flowGen rfl hm hp hb
      (by omega) hw]
  simp only [StateT.run_bind]
  rw [elabEnvArm_input_scope ctx f body pos hlen, splicedFrameScope_zero,
    elabBlockScope_run _ _ body hmF (openLengthScope_inert _ _ hlen)]
  have he : openScope { openScope st with spans := { (openScope st).spans with frames :=
      { (openScope st).spans.frames with nextBase := (openScope st).spans.frames.base } } } =
      openScope st := rfl
  have hg : ({ openScope st with spans := { (openScope st).spans with frames :=
      { (openScope st).spans.frames with nextBase := (openScope st).spans.frames.base } } }
      : ESt).flowGen = st.flowGen := rfl
  rw [he, hg]
  rcases hx : (elabBlocksGo { ctx with file := f, callSite := none } body 0 #[] #[]
    st.flowGen).run (openScope st) with ⟨bs, s4⟩
  have hend := fun s b => elabBlocksGo_blanks_end
    (pre ++ #[Raw.env (Parse.inputEnv f) body pos] ++ post) b _ (pre.size + 1) st.flowGen ctx s
    rfl hm (fun j hj hij => hblank j hj (by omega))
  simp only [StateT.run_bind, hx, closeBlockScope_base, hend, parFollows_include pre post _ hpost]
  rfl

public theorem elabBlocks_input_exact (ctx : Ctx) (f : String) (body pre post : Array Raw)
    (pos : Pos) (st : ESt) (h : InputSplice ctx body pos)
    (hpre : pre.all sourceBlank = true) (hpost : post.all sourceBlank = true) :
    (elabBlocks ctx (pre ++ #[.env (Parse.inputEnv f) body pos] ++ post)).run st =
      let r := (elabBlocks { ctx with file := f, callSite := none } body).run st
      (Ir.markDisplay false (post.any (· matches .par _)) false 0 r.1, r.2) := by
  rw [elabBlocks_run, elabBlocks_run]
  exact elabBlockScope_input_exact ctx f body pre post pos _ h hpre hpost

public theorem runDocBody_input_exact (plan : DocBodyPlan) (f : String) (body pre post : Array Raw)
    (pos : Pos) (st : ESt) (hraws : plan.raws = pre ++ #[.env (Parse.inputEnv f) body pos] ++ post)
    (h : InputSplice plan.ctx body pos)
    (hpre : pre.all sourceBlank = true) (hpost : post.all sourceBlank = true) :
    (runDocBody plan).run st =
      let r := (elabBlocks { plan.ctx with file := f, callSite := none } body).run st
      (finishDocBody plan
        (Ir.markDisplay false (post.any (· matches .par _)) false 0 r.1)).run r.2 := by
  unfold runDocBody
  rw [hraws]
  simp only [StateT.run_bind]
  rw [elabBlocks_input_exact plan.ctx f body pre post pos st h hpre hpost]
  rfl

public theorem markdownVocabulary_contract :
    (∀ n ∈ Md.vocabulary.envs, n ∈ builtinEnvNames ∨ ' ' ∈ n.toList) ∧
    (∀ n ∈ Md.vocabulary.ctrls ++ Md.vocabulary.bridged, Compat.lengthRestoreKeys? n = none) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      simp [builtinEnvNames, blockEnvs, Parse.markdownTableEnv, Parse.markdownDisclosureEnv]
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · simp only [Md.vocabulary, Md.citeCtrls, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Compat.lengthRestoreKeys?]
    · rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
        cases level <;> simp [Parse.headingControl, Compat.lengthRestoreKeys?]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl <;>
          simp [Parse.markdownBibControl, Parse.citeSetupMark, Compat.lengthRestoreKeys?]

private theorem bodyIsBlockList_of_mem : (l : List Raw) → (r : Raw) → r ∈ l →
    bodyIsBlockOne r = true → bodyIsBlockList l = true
  | [], _, h, _ => absurd h List.not_mem_nil
  | x :: rest, r, h, hr => by
    simp only [bodyIsBlockList, Bool.or_eq_true]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hr
    · exact Or.inr (bodyIsBlockList_of_mem rest r h hr)

private theorem bodyIsBlockOne_of_blockStart (r : Raw) (h : Md.BlockStart r) :
    bodyIsBlockOne r = true := by
  rcases h with ⟨p, rfl⟩ | ⟨n, p, rfl, hn⟩ | ⟨e, s, p, rfl, he⟩ | ⟨n, b, p, rfl, hn⟩
  · simp [bodyIsBlockOne]
  · rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
      cases level <;> simp [bodyIsBlockOne, blockHeading?, Parse.headingControl, Parse.headingControl?]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> simp [bodyIsBlockOne]
  · simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [bodyIsBlockOne]
  · simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      simp [bodyIsBlockOne, Parse.inputEnvFile?, blockEnvs, Parse.markdownEnv,
        Parse.markdownTableEnv, Parse.markdownDisclosureEnv]

private theorem bodyIsBlock_of_blockStart (body : Array Raw) (h : ∃ r ∈ body, Md.BlockStart r) :
    bodyIsBlock body = true := by
  obtain ⟨r, hr, hs⟩ := h
  exact bodyIsBlockList_of_mem body.toList r (Array.mem_toList_iff.mpr hr)
    (bodyIsBlockOne_of_blockStart r hs)

private theorem markdownInput_splice (ctx : Ctx) (f t : String) (cites : Bool) (pos : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Md.readIncluded f t cites).1 ≠ #[]) :
    InputSplice ctx (Md.readIncluded f t cites).1 pos := by
  have hread : (Md.readIncluded f t cites).1 = (Md.desugar f t .document .included cites).1 := by
    rw [Md.readIncluded_desugar_exact]
  rw [hread] at hne ⊢
  refine ⟨hm, hp, bodyIsBlock_of_blockStart _
    (Md.desugar_blockStart_contract f t .document .included cites none hne), ?_⟩
  intro n p hback
  have hmem : Raw.ctrl n p ∈ (Md.desugar f t .document .included cites).1 := by
    rw [Array.back?_eq_getElem?] at hback
    exact Array.mem_of_getElem? hback
  have hadm := Md.desugar_vocabulary_mem f t .document .included cites none _ hmem
  simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem] at hadm
  exact markdownVocabulary_contract.2 n (List.mem_append.mpr hadm)

private theorem markdownInput_scope_exact (ctx : Ctx) (f t : String) (cites : Bool) (pre post : Array Raw)
    (pos : Pos) (st : ESt)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Md.readIncluded f t cites).1 ≠ #[])
    (hpre : pre.all sourceBlank = true) (hpost : post.all sourceBlank = true) :
    (elabBlockScope ctx (pre ++ (Surface.fragment .markdown f t pos cites).1 ++ post)).run st =
      let r := (elabBlockScope { ctx with file := f, callSite := none }
        (Md.readIncluded f t cites).1).run st
      (Ir.markDisplay false (post.any (· matches .par _)) false 0 r.1, r.2) :=
  elabBlockScope_input_exact ctx f _ pre post pos st (markdownInput_splice ctx f t cites pos hm hp hne)
    hpre hpost

public theorem markdownInput_blocks_exact (ctx : Ctx) (f t : String) (cites : Bool) (pre post : Array Raw)
    (pos : Pos) (st : ESt)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Md.readIncluded f t cites).1 ≠ #[])
    (hpre : pre.all sourceBlank = true) (hpost : post.all sourceBlank = true) :
    (elabBlocks ctx (pre ++ (Surface.fragment .markdown f t pos cites).1 ++ post)).run st =
      let r := (elabBlocks { ctx with file := f, callSite := none }
        (Md.readIncluded f t cites).1).run st
      (Ir.markDisplay false (post.any (· matches .par _)) false 0 r.1, r.2) := by
  rw [elabBlocks_run, elabBlocks_run]
  exact markdownInput_scope_exact ctx f t cites pre post pos _ hm hp hne hpre hpost

public theorem markdownInput_blocks_text (ctx : Ctx) (f t : String) (cites : Bool) (pre post : Array Raw)
    (pos : Pos) (st : ESt)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Md.readIncluded f t cites).1 ≠ #[])
    (hpre : pre.all sourceBlank = true) (hpost : post.all sourceBlank = true) :
    Ir.blocksText
        ((elabBlocks ctx (pre ++ (Surface.fragment .markdown f t pos cites).1 ++ post)).run st).1 =
      Ir.blocksText ((elabBlocks { ctx with file := f, callSite := none }
        (Md.readIncluded f t cites).1).run st).1 := by
  rw [markdownInput_blocks_exact ctx f t cites pre post pos st hm hp hne hpre hpost]
  exact Ir.markDisplay_text false _ false 0 _

end LeanTex.Core.Elab
