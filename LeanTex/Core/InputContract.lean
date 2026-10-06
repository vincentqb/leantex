import LeanTex.Core.CompatContract

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
