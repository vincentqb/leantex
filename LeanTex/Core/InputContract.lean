module

public import LeanTex.Core.CompatContract
public import LeanTex.Core.Elab

import all LeanTex.Core.Elab
import all LeanTex.Core.Compat

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

end LeanTex.Core.Elab
