import LeanTex.Core.CompatContract
import LeanTex.Core.Elab

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
theorem inputRequest_names_asked (request : Compat.InputRequest) :
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
def Reported (ds : Array Diag) (producer : Diag) : Prop :=
  ∃ actual ∈ ds, { actual with sites := producer.sites } = producer

theorem reported_of_mem (ds : Array Diag) (d : Diag) (h : d ∈ ds) :
    Reported ds d :=
  ⟨d, h, rfl⟩

theorem reported_tally (ds : Array Diag) (d : Diag) (h : Reported ds d) :
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

theorem reported_append (left right : Array Diag) (d : Diag) (h : Reported left d) :
    Reported (left ++ right) d := by
  obtain ⟨actual, ha, heq⟩ := h
  exact ⟨actual, Array.mem_append.mpr (Or.inl ha), heq⟩

/-- Document completion preserves the diagnostics supplied by execution and
compatibility, including their original refused names, codes and spans.
Colour realization, recovered-content accounting and the first tally
cannot change any of those fields. -/
theorem completePrepared_reports_contract (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Ir.Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) (d : Diag)
    (h : d ∈ earlier ++ p.compatDiags) :
    Reported (completePrepared file p earlier doc table report st).2.1 d := by
  unfold completePrepared
  dsimp only
  apply reported_tally
  apply reported_of_mem
  apply accountRecovered_mem
  exact Array.mem_append.mpr (Or.inl
    (Array.mem_append.mpr (Or.inl
      (Array.mem_append.mpr (Or.inl
        (Array.mem_append.mpr (Or.inl
          (Array.mem_append.mpr (Or.inl
            (Array.mem_append.mpr (Or.inl h)))))))))))

/-- The production preamble and body interpreter reach the same diagnostic
completion for every picture-withdrawal environment. -/
theorem runPrepared_reports_contract (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (withdrawn : Array String)
    (d : Diag) (h : d ∈ earlier ++ p.compatDiags) :
    Reported (runPrepared file p earlier metric withdrawn).2.1 d := by
  obtain ⟨doc, table, report, st, heq⟩ :=
    runPrepared_complete_exact file p earlier metric withdrawn
  rw [heq]
  exact completePrepared_reports_contract file p earlier doc table report st d h

attribute [local irreducible] runPrepared

/-- Whichever production pass withdrawal selects, source erasure and the
reference judge preserve its producer records through the final tally. -/
theorem runPreparedFinal_reports_contract (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) (d : Diag)
    (h : d ∈ earlier ++ p.compatDiags) :
    Reported (runPreparedFinal file p earlier metric).2 d := by
  unfold runPreparedFinal finishPreparedRuns
  dsimp only
  split
  · exact reported_tally _ d (reported_append _ _ d
      (runPrepared_reports_contract file p earlier metric #[] d h))
  · exact reported_tally _ d (reported_append _ _ d
      (runPrepared_reports_contract file p earlier metric _ d h))

end LeanTex.Core.Elab
