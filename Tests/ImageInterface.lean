module

import LeanTex.Core.Image

namespace Tests.ImageInterface

open LeanTex.Core

-- The driver can probe, plan, select PDF pages, and persist raster plans
-- through an ordinary import.
example : ByteArray → Except String Image.Source := Image.probe
example : ByteArray → PdfRead.PageSelection → Except String Image.Source := Image.probePage
example : ByteArray → PdfRead.PageSelection → Except String Image.Source :=
  fun b page => Image.probePdf b page
example : Image.PlanParams → Image.Source → Except String Image.Plan := Image.plan
example : ByteArray → Except String Image.Plan := Image.decode
example : Image.Plan → ByteArray := Image.encodeBin
example : ByteArray → Option Image.Plan := Image.decodeBin
example : String → Image.Plan → Array Diag := Image.lossDiags

example (p : Image.Plan) (h : Image.binBounded p) :
    Image.decodeBin (Image.encodeBin p) = some p :=
  Image.decodeBin_encodeBin_id p h

example (p : Image.PlanParams) (s : Image.Source) (out : Image.Plan)
    (hf : s.format = .png) (hc : s.colorType = 0 ∨ s.colorType = 2 ∨ s.colorType = 3)
    (h : Image.plan p s = .ok out) : out.data = s.payload ∧ out.recoded = false :=
  Image.plan_passthrough_exact p s out hf hc h

-- The effect boundary preserves the requested assets and names missing ones.
example (fetched : Array (Image.Request × Image.Fetch)) :
    (Image.fulfilRequests fetched).1.entries.map (·.toRequest) = fetched.map (·.1) :=
  Image.fulfilRequests_covers fetched

example (fetched : Array (Image.Request × Image.Fetch)) :
    ∀ en ∈ (Image.fulfilRequests fetched).1.entries, en.info = none →
      ∃ d ∈ (Image.fulfilRequests fetched).2, d.subject = some en.src :=
  Image.fulfilRequests_named fetched

-- HtmlDoc and Pending use precisely these store and sizing equations.
example (store : Image.Store) (i : Nat) : store.get? i = store.entries[i]? := rfl

example (store : Image.Store) (src : String) :
    store.find? src = store.findRequest? { src } := rfl

example (store : Image.Store) (req : Image.Request) :
    store.infoRequest? req =
      (store.entries.find? (·.toRequest == req)).bind (·.info) := rfl

example (w h : Image.Len) (iW iH textW textH : Dim.Sp) :
    Image.resolveSize { width := some w, height := some h } iW iH textW textH =
      (w.resolve textW textH, h.resolve textW textH) := rfl

example (px : Nat) : Image.Plan.width { pxW := px, pxH := px } = Dim.pt px :=
  Image.width_at_default_dpi px

-- Normal consumers cannot name parser, scan, planner, or accumulator internals.
example : True := by
  fail_if_success have := Image.probePng
  fail_if_success have := Image.KeyState
  fail_if_success have := Image.keyScan
  fail_if_success have := Image.planPng
  fail_if_success have := Image.fulfilList
  fail_if_success have := Image.unfilterByte_project
  fail_if_success have := Image.readBin
  trivial

end Tests.ImageInterface
