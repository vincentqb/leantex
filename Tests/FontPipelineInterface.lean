module

import LeanTex.Cli.FontFix
import LeanTex.Cli.FontEnv
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.BrowserFaces

namespace Tests.FontPipelineInterface

open LeanTex.Core LeanTex.Cli

-- Driver measurement decisions use public contracts, not implementation bodies.
example : Array Ir.Block → Array FontFix.Probe := FontFix.probes
example : Ir.Pic.Picture → Array FontFix.Probe := FontFix.probesOfPic
example : Ir.Pic.LabelMetric → Ir.Pic.LabelMetric → Array FontFix.Probe → Bool :=
  FontFix.agree
example : Ir.Pic.LabelMetric → Ir.Pic.LabelMetric → Array FontFix.Probe → Nat :=
  FontFix.disagreements

example (metric : Ir.Pic.LabelMetric) (ps : Array FontFix.Probe) :
    FontFix.agree metric metric ps = true :=
  FontFix.agree_refl metric ps

example (a b : Ir.Pic.LabelMetric) (ps : Array FontFix.Probe)
    (h : FontFix.agree a b ps = true) (p : FontFix.Probe) (hp : p ∈ ps) :
    a p.1 p.2 = b p.1 p.2 :=
  FontFix.agree_probe a b ps h p hp

example (a b : Ir.Pic.LabelMetric) (content : Array Ir.Inline)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (w h : Dim.Sp)
    (same : a content scale = b content scale) :
    Ir.Pic.nodeExtent a content scale align w h =
      Ir.Pic.nodeExtent b content scale align w h :=
  FontFix.extent_agree a b content scale align w h same

example (pic : Ir.Pic.Picture) (x y : Dim.Sp) (content : Array Ir.Inline)
    (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign)
    (h : Ir.Pic.Shape.label x y content color scale align ∈ pic.shapes) :
    (content, scale) ∈ FontFix.probesOfPic pic :=
  FontFix.probesOfPic_covers pic x y content color scale align h

example : True := by
  fail_if_success have := FontFix.instDecidableEqLabelInk
  trivial

-- The scan and filesystem remain explicit inputs to the effect boundary.
example : IO FontEnv.Cache := FontEnv.Cache.mk'
example : FontEnv.Cache → String → IO (Except String Font.Font) := FontEnv.Cache.parse
example : FontEnv.Cache → Array FontDb.Face → String → Option String → Nat → Bool →
    IO (Option (FontDb.Face × Option FontDb.Substituted)) :=
  FontEnv.Cache.resolveWeight
example : String → IO (Except Diag (Font.Font × String)) := FontEnv.loadOverride
example : String → Array String → IO (List String × Array Diag) := FontEnv.resolveDocDirs
example : Array FontDb.Face → Option String → Option String → Bool →
    Array Font.Font → Array String → Array String → Option FontEnv.Cache →
    IO FontEnv.MathFace :=
  fun faces declared body wantsMath fonts paths missing cache =>
    FontEnv.resolveMath faces declared body wantsMath fonts paths missing cache
example : Array FontDb.Face → Option String → Option String → Bool →
    Array Font.Font → Array String → Array String → IO FontEnv.MathFace :=
  fun faces declared body wantsMath fonts paths missing =>
    FontEnv.resolveMath faces declared body wantsMath fonts paths missing
example (answer : FontEnv.MathFace) :
    Array Font.Font × Array String × Option Nat × Array String × Array Diag :=
  (answer.fonts, answer.paths, answer.index, answer.missing, answer.diags)

example : FontAssembly.FaceScan := { faces := #[], docDirs := [], dirs := #[], diags := #[] }
example : FontAssembly.Purpose := .settled
example : FontAssembly.Purpose := .provisional true
example : Ir.Doc → FontAssembly.FaceScan → FontEnv.Cache → FontAssembly.Purpose →
    IO (Except Diag (Font.FontSet × Ir.Doc × Array Diag × String)) :=
  FontAssembly.buildFontSet

-- The browser oracle reads the same plan and preservation contracts as the driver.
example : BrowserFaces.Conversion := .svgPoster .first
example : BrowserFaces.Conversion := .pdfPage .last
example : BrowserFaces.Conversion → String := BrowserFaces.Conversion.key
example : BrowserFaces.Plan → String := BrowserFaces.Plan.key
example : BrowserFaces.Plan → Option BrowserFaces.Conversion := BrowserFaces.Plan.conversion?
example : Image.Loaded → BrowserFaces.Plan := BrowserFaces.plan
example : BrowserFaces.Outcome := { bytes := .error "unavailable" }
example : Image.Loaded → BrowserFaces.Plan → BrowserFaces.Outcome → Image.Loaded :=
  BrowserFaces.apply
example : Image.Loaded → IO Image.Loaded := BrowserFaces.prepare
example : Array Image.Loaded → Nat → IO (Array Image.Loaded) :=
  fun entries limit => BrowserFaces.prepareAll entries limit
example : Array Image.Loaded → IO (Array Image.Loaded) :=
  fun entries => BrowserFaces.prepareAll entries

example (en : Image.Loaded) (plan : BrowserFaces.Plan) (answer : BrowserFaces.Outcome) :
    (BrowserFaces.apply en plan answer).info = en.info :=
  BrowserFaces.apply_info_exact en plan answer

example (en : Image.Loaded) (plan : BrowserFaces.Plan) (answer : BrowserFaces.Outcome) :
    (BrowserFaces.apply en plan answer).canvasSize = en.canvasSize :=
  BrowserFaces.apply_canvas_exact en plan answer

example (a b : ByteArray) (i j : Nat) :
    BrowserFaces.sourceKey (some a) i = BrowserFaces.sourceKey (some b) j ↔
      Flate.contentKey a = Flate.contentKey b :=
  BrowserFaces.sourceKey_contract a b i j

-- Ordinary callers cannot forge a cache or depend on its mutable representation.
example : True := by
  fail_if_success have := FontEnv.Cache.mk
  trivial

example : True := by
  fail_if_success have := FontEnv.Cache.ref
  trivial

example : True := by
  fail_if_success have := FontEnv.Cache.weights
  trivial

example : True := by
  fail_if_success have := FontEnv.parseFace
  trivial

example : True := by
  fail_if_success have := FontAssembly.singleFaceIndex
  trivial

example : True := by
  fail_if_success have := FontAssembly.noFontDiag
  trivial

example (_parsed : IO.Ref (Array (String × Font.Font)))
    (_answers : IO.Ref (Array ((String × Option String × Nat × Bool) ×
      Option (FontDb.Face × Option FontDb.Substituted)))) : True := by
  fail_if_success have : FontEnv.Cache := ⟨_parsed, _answers⟩
  trivial

example : True := by
  fail_if_success have := BrowserFaces.Conversion.source?
  fail_if_success have := BrowserFaces.mapBySource
  fail_if_success have := BrowserFaces.primarySource?
  fail_if_success have := BrowserFaces.Prepared
  fail_if_success have := BrowserFaces.preparePrimary
  fail_if_success have := BrowserFaces.Prepared.companion?
  fail_if_success have := BrowserFaces.Prepared.finish
  trivial

end Tests.FontPipelineInterface
