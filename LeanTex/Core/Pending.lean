module

public import LeanTex.Core.BibStyle
import all LeanTex.Core.Ir

/-! # The resolution gate

Nothing unresolved reaches a backend unnamed. The resolution points are
few — `\ref` (the label table), `\cite` (`Bib.apply`), images and
boundary pictures (`Image.fulfil`) — and each names what it leaves: W0349,
W0351, W0601/W0602/W0378/W0379. `pending_named` is the one statement over
the pipeline's pure tail holding the census (`Ir.pending`) to those
diagnostics, assembled from each resolver's own lemma:

- `Ir.refDiags_named` — every `.ref` still showing `??` has a W0349 whose
  subject is its key; the judge reads the same census.
- `Bib.apply_no_cite` — no `.cite` survives resolution, in any region.
- `Image.fulfilRequests_named` and `Image.fulfilRequests_covers` — every store entry with
  no payload has a diagnostic whose subject is its source, and the store
  has an entry per fetched source.

The driver (`Main.frontend`, `Main.build`) is the statement's shape:
`Bib.apply` on the elaborated document, `Ir.refDiags` over its output,
then `Image.fulfilRequests` over one read per `Ir.imageRequests` entry — which is the
hypothesis `hcov`, the one fact the driver contributes. -/

namespace LeanTex.Core

open Ir

/-- **Every pending thing is named.** Over the document the backends read
(`Bib.apply`'s output) and the store they read (`Image.fulfilRequests`'s), every
element of the pending census has a diagnostic in the run's output whose
structured subject is its key. -/
public theorem pending_named (table : RefTable) (spanOf : String → Option Span)
    (sources : Array (String × String)) (doc : Doc)
    (fetched : Array (Image.Request × Image.Fetch))
    (hcov : fetched.map (·.1) = imageRequests (Bib.apply sources doc).1) :
    ∀ p ∈ pending (Bib.apply sources doc).1 (Image.fulfilRequests fetched).1,
      ∃ d ∈ refDiags table spanOf (Bib.apply sources doc).1 ++ (Image.fulfilRequests fetched).2,
        d.mentions p = true := by
  intro p hp
  unfold pending at hp
  rw [Array.mem_append] at hp
  rcases hp with hn | hi
  · rw [Array.mem_map] at hn
    obtain ⟨u, hu, rfl⟩ := hn
    have hnc := Bib.apply_no_cite sources doc u hu
    cases u with
    | cite k => simp [Unresolved.isCite] at hnc
    | ref k =>
      obtain ⟨d, hd, hm⟩ := refDiags_named table spanOf _ k hu
      exact ⟨d, Array.mem_append_left _ hd, hm⟩
  · unfold pendingImages at hi
    rw [Array.mem_map] at hi
    obtain ⟨src, hsrc, rfl⟩ := hi
    rw [Array.mem_filter] at hsrc
    obtain ⟨hmem, hnone⟩ := hsrc
    rw [← hcov, ← Image.fulfilRequests_covers, Array.mem_map] at hmem
    obtain ⟨en, hen, rfl⟩ := hmem
    unfold Image.Store.infoRequest? at hnone
    cases hf : (Image.fulfilRequests fetched).1.entries.find? (·.toRequest == en.toRequest) with
    | none =>
      rw [Array.find?_eq_none] at hf
      exact absurd (beq_self_eq_true en.toRequest) (hf en hen)
    | some en' =>
      rw [hf] at hnone
      simp only [Option.bind, Option.isNone_iff_eq_none] at hnone
      obtain ⟨d, hd, hs⟩ :=
        Image.fulfilRequests_named fetched en' (Array.mem_of_find?_eq_some hf) hnone
      have hsrc := Array.find?_some hf
      have hsources := congrArg Image.Request.src (eq_of_beq hsrc)
      refine ⟨d, Array.mem_append_right _ hd, ?_⟩
      simp [Diag.mentions, Pending.key, hs, hsources]

end LeanTex.Core
