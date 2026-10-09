module

public import LeanTex.Core.CompatContract
public import LeanTex.Core.Elab
public import LeanTex.Core.Surface
public import LeanTex.Core.MdDesugarContract

import all LeanTex.Core.Elab
import all LeanTex.Core.Compat
import all LeanTex.Core.Parse
import all LeanTex.Core.Ir

namespace LeanTex.Core.CompatContract

/-- Candidate coverage for an actual callback argument, including loads
introduced by expansion. The request has one executed operand slice: its
filename, options and the call the driver's `expandLocalSty` scans are
projections of that slice. No equality to an unexpanded source census is
assumed.

This is the request boundary contract. It does not infer a file attempt
from a refusal code: native `\theme` and native-package option refusals
remain outside the loading door. Nor does it claim that the filesystem
contained or successfully supplied any candidate. -/
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

/-- A final tally may move a site's count to its carrier, but it must retain
the producer's whole diagnostic record. In particular the refused name and
source span cannot be reconstructed from the message or from another code
at the same site. -/
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

/-- Document completion preserves the diagnostics supplied by execution and
compatibility, including their original refused names, codes and spans.
Colour realization, recovered-content accounting and the first tally
cannot change any of those fields. The trigger is restored from the
prepared source's lexical evidence. -/
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
            (Array.mem_append.mpr (Or.inl h)))))))))))

/-- The production preamble and body interpreter reach the same diagnostic
completion for every picture-withdrawal environment. -/
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

/-- Whichever production pass withdrawal selects, source erasure and the
reference judge preserve its producer records through the final tally. -/
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
/-- Preparation retains every compatibility producer record verbatim. The
text pass can add reports, but cannot replace the package producer's span,
refused spelling, code or source trigger. -/
public theorem prepareRewritten_diags_covers (file : String)
    (scan : Compat.BoundaryScan) (macros : Array (String × String))
    (triggers : Compat.SourceTriggers) (prior : Array Diag)
    (rewritten : Array Parse.Raw × Array Diag × Array String)
    (attempts : Array Compat.InputAttempt) (d : Diag)
    (h : d ∈ rewritten.2.1) :
    d ∈ (prepareRewritten file scan macros triggers prior rewritten attempts).compatDiags := by
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
  prepareRewritten_diags_covers file _ _ _ _ _ _ d h

attribute [local irreducible] prepareExecuted runPreparedFinal in
/-- A compatibility refusal reaches the final executed-document result,
through text rewriting, body interpretation, recovery and both tallies.
The caller still owes the producer-to-request connection; this lemma
preserves the actual record rather than inventing a matching report. -/
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
/-- A live external-package declaration whose reader returns no input has
an actual failed-call receipt, the requested style-file candidate for each
name, and its producer's full source-located refusal in the final result.
The final trigger uses the same lexical evidence as the producer, so
the only further change is the tally's site count.

The domain is stated on the source call and the external reader before
execution: either package-loading spelling, arbitrary nonempty external
comma-separated names and arbitrary positions. It excludes native-package
option refusals, native theme selection, dormant definitions and calls
inside consumed control operands. Those cases cannot justify a global
equivalence between requests and refusal codes. -/
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
      pos groupPos namePos _ #[] hc hnames hr
  refine ⟨hproducer.1, ?_⟩
  intro part hpart
  have hname : request.name = names.trimAscii.toString :=
    Compat.InputRequest.package_name_exact file command names pos groupPos namePos
  constructor
  · exact (CompatContract.inputRequest_names_asked request).1 hc part
      (by simpa only [hname] using hpart) (hnames part hpart).1 (hnames part hpart).2.1
  · simpa only [Compat.SourceTriggers.attribute_fixed_point] using
      runExecuted_reports_contract file _ earlier metric _ (hproducer.2 part hpart)

/-! ## Including is transparent

An included file reaches the elaborator wrapped once, as the file it came
from (`Parse.inputEnv`, through `Surface.fragment`). The statements below
say what the wrapper means: nothing but the file's name. An include
standing as the whole of a block accumulator produces exactly the blocks and
the final state its raws produce as that accumulator of their own, under the
file's name, with no call site; the host contributes only its display
marking of a file that is exactly one display. The accumulator is any the
elaborator opens through `elabBlockScope` with no text pending
(`elabBlockScope_input_exact`, from every frame-source state): a frame's
content — the frame arm elaborates it there — and the bodies the block
environments open the same way. The document body is the public form
(`elabBlocks_input_exact`, `runDocBody_input_exact`). That a frame's other
steps — options, title, notes, palette — read only its content scope's
result is the frame arm's code, not a statement here; the doors' D6 frame
rows check the composed frame end to end.

Mid-sequence, the included blocks are the same, but the inner frame-source
offsets shift by the blocks before the include, by design; that form is a
stretch lemma, not a claim made here. Markdown meets the hypotheses by
construction (`markdownInput_blocks_exact`): a nonempty file's desugaring
is block-shaped and lowers into a vocabulary that holds no length-restore
marker. -/

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

private theorem pictureInSentence_input (ctx : Ctx) (f : String) (cur raws : Array Raw) (i : Nat)
    (pos : Pos) : pictureInSentence ctx (Parse.inputEnv f) cur raws i pos = pure () := by
  simp [pictureInSentence, inputEnv_ne_tikzpicture]

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

/-- The block spine at an include wrapper standing alone: no paragraph is
open, nothing flushes, and the environment arm runs on an empty
accumulator; the result is marked as a display would be, and the walk
moves past the wrapper. -/
private theorem elabBlocksGo_input_splice (ctx : Ctx) (st : ESt) (f : String) (body : Array Raw)
    (pos : Pos) (gen : Nat) (hg : st.flowGen = gen)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hb : bodyIsBlock body = true) :
    (elabBlocksGo ctx #[.env (Parse.inputEnv f) body pos] 0 #[] #[] gen).run st =
      ((do
        let bs ← elabEnvArm ctx (Parse.inputEnv f) body pos #[]
        elabBlocksGo ctx #[.env (Parse.inputEnv f) body pos] 1
          (Ir.markDisplay false false false 0 bs) #[] gen) : EM (Array Block)).run st := by
  subst hg
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 0 #[] #[] hm (by simp) (by simpa [Raw.origins?] using hp)]
  simp only [pure_bind]
  simp [inputEnv_ne_linkedBoxRowMark, inputEnvFile?_inputEnv, hb, pictureInSentence_input,
    flushPara_empty ctx _ hm, Ir.flushedText, parFollows, Ir.markInParagraph]

/-- The environment arm of an include wrapper: the file's raws in a fresh
scope under the file's name, spliced at offset zero, and nothing else. -/
private theorem elabEnvArm_input_scope (ctx : Ctx) (f : String) (body : Array Raw) (pos : Pos)
    (hlen : lengthScopeKeys? body = none) :
    elabEnvArm ctx (Parse.inputEnv f) body pos #[] =
      splicedFrameScope (some 0) (elabBlockScope { ctx with file := f, callSite := none } body) := by
  rw [elabEnvArm, openLengthScope_inert ctx body hlen]
  simp [inputEnv_ne_scopeEnv, inputEnvFile?_inputEnv, closeLengthScope]
  rfl

/-- The block spine past its last raw, with no paragraph open and no
macro role active: whatever the flow generation, it returns its blocks and
leaves the state alone. -/
private theorem elabBlocksGo_end (ctx : Ctx) (st : ESt) (raws : Array Raw) (i : Nat)
    (blocks : Array Block) (gen : Nat)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hi : raws.size ≤ i) :
    (elabBlocksGo ctx raws i blocks #[] gen).run st = (blocks, st) := by
  have hf : (flowCtx ctx st gen).macroRoles = ({file := ""} : Ctx).macroRoles := by
    unfold flowCtx
    split <;> exact hm
  rw [elabBlocksGo, run_get]
  simp only [show ¬ i < raws.size from Nat.not_lt.mpr hi, ↓reduceDIte]
  simp [blockMacroStep, flowMCtx, hf, blockMacroKinds, hi, flushPara,
    closeBlockFrameSources, commonOrigins, moveMacroRuns, closeMacroRuns, MacroRoles.empty]
  rfl

private theorem closeBlockScope_base (ctx : Ctx) (base : Option Nat) (blocks : Array Block)
    (st : ESt) :
    (closeBlockScope ctx #[] base blocks).run st =
      (blocks, { st with spans := { st.spans with frames := { st.spans.frames with base } } }) := by
  simp [closeBlockScope, closeLengthScope, setFrameSourceBase]
  rfl

/-- A block accumulator's entry state: its scheduled splice offset becomes
its base, and nothing is scheduled inside (`openBlockScope`). -/
private def openScope (st : ESt) : ESt :=
  { st with spans := { st.spans with frames :=
    { st.spans.frames with base := st.spans.frames.nextBase, nextBase := none } } }

/-- A block accumulator with no macro role active and no length scope to
open runs its walk from the entry state and closes back to the base it
found. -/
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

/-- A splice at offset zero schedules the accumulator it opens at the base
it is met at: the included file's scope opens where its caller's stands. -/
private theorem splicedFrameScope_zero (scope : EM (Array Block)) (st : ESt) :
    (splicedFrameScope (some 0) scope).run st =
      scope.run { st with spans := { st.spans with frames :=
        { st.spans.frames with nextBase := st.spans.frames.base } } } := by
  cases hb : st.spans.frames.base <;>
    simp [splicedFrameScope, FrameSources.offset, hb]

/-- `elabBlocks` is the accumulator scheduled at offset zero. -/
private theorem elabBlocks_run (ctx : Ctx) (raws : Array Raw) (st : ESt) :
    (elabBlocks ctx raws).run st =
      (elabBlockScope ctx raws).run { st with spans := { st.spans with frames :=
        { st.spans.frames with nextBase := some 0 } } } := rfl

/-- The dispatch domain where a wrapped file splices. No macro expansion is
open; the wrapper has a source position; the raws are block-shaped (a
phrase joins the open paragraph, as TeX's `\input` of a phrase does); and
no trailing length-restore marker closes them. Each conjunct is a fact of
syntax and context, none a fact of the result. -/
@[expose] public def InputSplice (ctx : Ctx) (body : Array Raw) (pos : Pos) : Prop :=
  ctx.macroRoles = ({file := ""} : Ctx).macroRoles ∧ pos.origins = [] ∧ bodyIsBlock body = true ∧
    ∀ n p, body.back? = some (.ctrl n p) → Compat.lengthRestoreKeys? n = none

/-- **An include standing as a whole block accumulator is transparent.**
Its raws produce exactly the blocks and final state they produce as that
accumulator of their own, under the file's name and no call site, from any
frame-source state — so at a frame's content scope as at a document body.
The host contributes only its display marking of a file that is exactly one
display. The statement is the whole state, not a census: diagnostics,
counters, labels, frame sources and the flow epoch all agree. -/
private theorem elabBlockScope_input_exact (ctx : Ctx) (f : String) (body : Array Raw)
    (pos : Pos) (st : ESt) (h : InputSplice ctx body pos) :
    (elabBlockScope ctx #[.env (Parse.inputEnv f) body pos]).run st =
      let r := (elabBlockScope { ctx with file := f, callSite := none } body).run st
      (Ir.markDisplay false false false 0 r.1, r.2) := by
  obtain ⟨hm, hp, hb, hl⟩ := h
  have hlen := lengthScopeKeys?_back body hl
  have hmF : ({ ctx with file := f, callSite := none } : Ctx).macroRoles =
      ({file := ""} : Ctx).macroRoles := hm
  rw [elabBlockScope_run ctx st _ hm (openLengthScope_inert _ _ rfl),
    elabBlockScope_run _ st body hmF (openLengthScope_inert _ _ hlen)]
  simp only [StateT.run_bind]
  rw [elabBlocksGo_input_splice ctx (openScope st) f body pos st.flowGen rfl hm hp hb]
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
  have hend := fun s b => elabBlocksGo_end ctx s #[.env (Parse.inputEnv f) body pos] 1 b
    st.flowGen hm (by simp)
  simp only [StateT.run_bind, hx, closeBlockScope_base, hend]
  rfl

/-- **An include standing as its own block sequence is transparent**, at the
document body: the accumulator `elabBlocks` schedules at offset zero is the
one `elabBlockScope_input_exact` describes. -/
public theorem elabBlocks_input_exact (ctx : Ctx) (f : String) (body : Array Raw) (pos : Pos)
    (st : ESt) (h : InputSplice ctx body pos) :
    (elabBlocks ctx #[.env (Parse.inputEnv f) body pos]).run st =
      let r := (elabBlocks { ctx with file := f, callSite := none } body).run st
      (Ir.markDisplay false false false 0 r.1, r.2) := by
  rw [elabBlocks_run, elabBlocks_run]
  exact elabBlockScope_input_exact ctx f body pos _ h

/-- The same at the document body: a body that is one include runs the
document continuation — numbering, metadata, references — over exactly the
blocks the included raws produce as a body of their own. -/
public theorem runDocBody_input_exact (plan : DocBodyPlan) (f : String) (body : Array Raw)
    (pos : Pos) (st : ESt) (hraws : plan.raws = #[.env (Parse.inputEnv f) body pos])
    (h : InputSplice plan.ctx body pos) :
    (runDocBody plan).run st =
      let r := (elabBlocks { plan.ctx with file := f, callSite := none } body).run st
      (finishDocBody plan (Ir.markDisplay false false false 0 r.1)).run r.2 := by
  unfold runDocBody
  rw [hraws]
  simp only [StateT.run_bind]
  rw [elabBlocks_input_exact plan.ctx f body pos st h]
  rfl

/-- Markdown's vocabulary against the elaborator's reserved names: its
environments are the elaborator's own (a document cannot redefine them),
and none of its controls is a length-restore marker. -/
public theorem markdownVocabulary_contract :
    (∀ n ∈ Md.vocabulary.envs, n ∈ builtinEnvNames) ∧
    (∀ n ∈ Md.vocabulary.ctrls ++ Md.vocabulary.bridged, Compat.lengthRestoreKeys? n = none) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp [builtinEnvNames, blockEnvs]
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Compat.lengthRestoreKeys?]
    · obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
      cases level <;> simp [Parse.headingControl, Compat.lengthRestoreKeys?]

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
  · obtain ⟨level, _, rfl⟩ := List.mem_map.mp hn
    cases level <;> simp [bodyIsBlockOne, blockHeading?, Parse.headingControl, Parse.headingControl?]
  · simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [bodyIsBlockOne]
  · simp only [Md.vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp [bodyIsBlockOne, Parse.inputEnvFile?, blockEnvs]

private theorem bodyIsBlock_of_blockStart (body : Array Raw) (h : ∃ r ∈ body, Md.BlockStart r) :
    bodyIsBlock body = true := by
  obtain ⟨r, hr, hs⟩ := h
  exact bodyIsBlockList_of_mem body.toList r (Array.mem_toList_iff.mpr hr)
    (bodyIsBlockOne_of_blockStart r hs)

/-- A nonempty markdown file meets the splice domain wherever no macro
expansion is open and the include has a source position: block-shaped by
`Md.desugar_blockStart_contract`, and closed by no length-restore marker by
`Md.desugar_vocabulary_mem` and `markdownVocabulary_contract`. -/
private theorem markdownInput_splice (ctx : Ctx) (f t : String) (pos : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Surface.read .md f t).1 ≠ #[]) :
    InputSplice ctx (Surface.read .md f t).1 pos := by
  have hread : (Surface.read .md f t).1 = (Md.desugar f t).1 := by
    simp [Surface.read, Md.read_desugar_exact]
  rw [hread] at hne ⊢
  refine ⟨hm, hp, bodyIsBlock_of_blockStart _ (Md.desugar_blockStart_contract f t hne), ?_⟩
  intro n p hback
  have hmem : Raw.ctrl n p ∈ (Md.desugar f t).1 := by
    rw [Array.back?_eq_getElem?] at hback
    exact Array.mem_of_getElem? hback
  have hadm := Md.desugar_vocabulary_mem f t _ hmem
  simp only [Md.Vocab.admits, Bool.or_eq_true, List.contains_iff_mem] at hadm
  exact markdownVocabulary_contract.2 n (List.mem_append.mpr hadm)

/-- Markdown at any block accumulator — a frame's content as a document
body: a nonempty markdown file read through its door and included where it
stands as the accumulator's whole content gives exactly the blocks and state
it gives alone there, under its own name, up to the host's display marking. -/
private theorem markdownInput_scope_exact (ctx : Ctx) (f t : String) (pos : Pos) (st : ESt)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Surface.read .md f t).1 ≠ #[]) :
    (elabBlockScope ctx (Surface.fragment .md f t pos).1).run st =
      let r := (elabBlockScope { ctx with file := f, callSite := none }
        (Surface.read .md f t).1).run st
      (Ir.markDisplay false false false 0 r.1, r.2) :=
  elabBlockScope_input_exact ctx f _ pos st (markdownInput_splice ctx f t pos hm hp hne)

/-- **Markdown included in tex is markdown.** A nonempty markdown file read
through its door and included where it stands as the block sequence gives
exactly the blocks and state it gives alone, under its own name, up to the
host's display marking. What remains assumed is the shape of the call, never
the file's content beyond its having some: no macro expansion open, a
source position, and a desugaring that is not empty. -/
public theorem markdownInput_blocks_exact (ctx : Ctx) (f t : String) (pos : Pos) (st : ESt)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Surface.read .md f t).1 ≠ #[]) :
    (elabBlocks ctx (Surface.fragment .md f t pos).1).run st =
      let r := (elabBlocks { ctx with file := f, callSite := none } (Surface.read .md f t).1).run st
      (Ir.markDisplay false false false 0 r.1, r.2) := by
  rw [elabBlocks_run, elabBlocks_run]
  exact markdownInput_scope_exact ctx f t pos _ hm hp hne

/-- The census of the same: included markdown sets the text it sets alone. -/
public theorem markdownInput_blocks_text (ctx : Ctx) (f t : String) (pos : Pos) (st : ESt)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : pos.origins = [])
    (hne : (Surface.read .md f t).1 ≠ #[]) :
    Ir.blocksText ((elabBlocks ctx (Surface.fragment .md f t pos).1).run st).1 =
      Ir.blocksText
        ((elabBlocks { ctx with file := f, callSite := none } (Surface.read .md f t).1).run st).1 := by
  rw [markdownInput_blocks_exact ctx f t pos st hm hp hne]
  exact Ir.markDisplay_text false false false 0 _

end LeanTex.Core.Elab
