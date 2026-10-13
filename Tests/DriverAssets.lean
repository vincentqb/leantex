module

public import LeanTex.Core.Image
public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Core.Font
import LeanTex.Core.Elab
import LeanTex.Cli.FontEnv
public import LeanTex.Cli.Args
import all LeanTex.Cli.Driver

/-! Test access to the driver's captured-image preparation and settle decision, without exporting
its orchestration state. -/

namespace Tests.DriverAssets

open LeanTex.Core

public def imageBrowserFaces (imgs : Image.Store) : IO Image.Store :=
  LeanTex.Cli.Driver.imageBrowserFaces imgs

/-- The artifacts a run writing `emit` reports scoped diagnostics for. -/
public def diagnosticOutputs (emit : Array LeanTex.Cli.Emit) : Array Diag.Output :=
  LeanTex.Cli.Driver.diagnosticOutputs emit

public def picsToSvg (pics : Array (String × ByteArray)) (imgs : Image.Store)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Array String) :=
  LeanTex.Cli.Driver.picsToSvg
    (pics.map fun (src, bytes) => { src, bytes }) imgs imageSpans

/-- Whether a document elaborated against `provisional` stands under the driver's settle decision
(`Driver.settlement`). -/
public def settles (elaborated : Ir.Doc) (provisional : Option Ir.Pic.LabelMetric)
    (fs : Font.FontSet) (resolved : Ir.Doc) : IO Bool := do
  let front : LeanTex.Cli.Driver.Front := {
    doc := elaborated, diags := #[], spans := {}, prepared := Elab.prepare "t" #[]
    earlier := #[], spliced := #[], ledger := {}, reads := #[], cache := ← LeanTex.Cli.FontEnv.Cache.mk'
    scan := none, provisional }
  return (LeanTex.Cli.Driver.settlement front fs resolved).2.2

end Tests.DriverAssets
