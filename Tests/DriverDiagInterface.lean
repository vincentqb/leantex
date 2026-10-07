module

import LeanTex.Cli.DriverDiag

/-! An ordinary driver client constructs typed diagnostics and uses the
source-location contract. Formatting and decision bodies stay opaque. -/

open LeanTex.Core LeanTex.Cli

namespace Tests.DriverDiagInterface

example : String → String → Diag := DriverDiag.unreadableInput
example : String → Diag := DriverDiag.outputPathsConflict
example : Pdf.WriteError → Diag := DriverDiag.pdfWriteRefused
example : String → String → Diag := DriverDiag.envFontUnusable
example : String → Diag := DriverDiag.envFontMissing
example : Diag := DriverDiag.noFont
example : String → String → Diag := DriverDiag.fontsDirMissing
example : String → List String → Nat → Diag := DriverDiag.familyMissing
example : String → String → Diag := DriverDiag.fontFileUnusable
example : String → Nat → FontDb.Face → Diag := DriverDiag.weightSubstituted
example : String → String → String → String → Option String → Diag :=
  DriverDiag.slotCollapsed
example : FontDb.Substituted → Diag := DriverDiag.substituted
example : String → String → Diag := DriverDiag.mathFaceNoTable
example : String → String → Diag := DriverDiag.mathFaceCompanion
example : String → Diag := DriverDiag.mathFaceFirst
example : String → Option Span → Diag := @DriverDiag.boundaryToolUnavailable
example : String → String → Option Span → Diag := @DriverDiag.boundaryFailed
example : String → String → Option Span → Diag := @DriverDiag.boundaryUnfinished
example : String → Option String → String → Option Span → Diag :=
  @DriverDiag.boundaryWithdrawn
example : String → Diag := DriverDiag.boundarySvgMissing
example : String → String → Diag := DriverDiag.listingHighlightUnavailable
example : String → Diag := DriverDiag.htmlResourceUnavailable
example : String → Option Span → String → Diag := @DriverDiag.inputMissing
example : String → String → Option Span → Diag := DriverDiag.bibMissing
example : String → String → Option Span → Diag := DriverDiag.dataMissing
example : Diag := DriverDiag.inputTooDeep
example : String → Diag := DriverDiag.allowUnfired
example : Array (String × Span) → String → Diag → Diag := DriverDiag.atImageRequest

example (spans : Array (String × Span)) (src : String) (d : Diag) (span : Span) :
    DriverDiag.atImageRequest spans src { d with span := some span } =
      { d with span := some span } := by
  fail_if_success rfl
  exact DriverDiag.atImageRequest_located_exact spans src d span

end Tests.DriverDiagInterface
