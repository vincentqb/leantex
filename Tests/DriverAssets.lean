module

public import LeanTex.Core.Image
public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Core.Font
import LeanTex.Core.Elab
import LeanTex.Cli.FontEnv
import all LeanTex.Cli.Driver

/-! Test access to the driver's captured-image preparation and its settle
decision. Legacy runtime tests use these wrappers without exporting the
driver's orchestration state. -/

namespace Tests.DriverAssets

open LeanTex.Core

public def imageBrowserFaces (imgs : Image.Store) : IO Image.Store :=
  LeanTex.Cli.Driver.imageBrowserFaces imgs

public def picsToSvg (pics : Array (String × ByteArray)) (imgs : Image.Store)
    (imageSpans : Array (String × Span) := #[]) :
    IO (Image.Store × Array Diag × Array String) :=
  LeanTex.Cli.Driver.picsToSvg
    (pics.map fun (src, bytes) => { src, bytes }) imgs imageSpans

/-- The driver's settle decision (`Driver.settlement`) for a document
elaborated against `provisional`, over the font set and the document font
assembly returned: whether that elaboration stands. -/
public def settles (elaborated : Ir.Doc) (provisional : Option Ir.Pic.LabelMetric)
    (fs : Font.FontSet) (resolved : Ir.Doc) : IO Bool := do
  let front : LeanTex.Cli.Driver.Front := {
    doc := elaborated, diags := #[], spans := {}, prepared := Elab.prepare "t" #[]
    earlier := #[], spliced := #[], ledger := {}, cache := ← LeanTex.Cli.FontEnv.Cache.mk'
    scan := none, provisional }
  return (LeanTex.Cli.Driver.settlement front fs resolved).2.2

end Tests.DriverAssets
