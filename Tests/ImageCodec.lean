module

public import Tests.Support

public section

open LeanTex.Core

/-! The LTIMG3 byte contract, captured before the reader/writer factorization.
These fixtures pin the persisted representation independently of round-trip
agreement between an encoder and decoder changed together. -/

private def profiledPlan : Image.Plan :=
  { pxW := 258, pxH := 772, dpiX := 150, dpiY := 96, bitDepth := 4
    color := .iccBased 3 (bytes [21, 22]), filter := .dct
    alpha := .soft (bytes [31, 32, 33]) 8, recoded := true
    orientation := 6, losses := #[.orientationDropped, .iccDropped], data := bytes [41, 42] }

private def indexedPlan : Image.Plan :=
  { profiledPlan with
    color := .indexed (bytes [0, 1, 2, 3, 4, 5])
    alpha := .colorKey #[0, 255, 65536, 4294967295]
    filter := .flatePredictor
    recoded := false }

private def profiledBytes : ByteArray := bytes
  [76, 84, 73, 77, 71, 51, 3, 1, 2, 1,
   0, 0, 1, 2, 0, 0, 3, 4, 0, 0, 0, 150, 0, 0, 0, 96, 0, 0, 0, 4, 0, 0, 0, 6,
   0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 3,
   0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 21, 22, 31, 32, 33, 41, 42]

private def indexedBytes : ByteArray := bytes
  [76, 84, 73, 77, 71, 51, 2, 0, 1, 0,
   0, 0, 1, 2, 0, 0, 3, 4, 0, 0, 0, 150, 0, 0, 0, 96, 0, 0, 0, 4, 0, 0, 0, 6,
   0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 255, 0, 1, 0, 0, 255, 255, 255, 255,
   1, 0, 0, 1, 2, 3, 4, 5, 41, 42]

private def sameRaster (a b : Image.Plan) : Bool :=
  a.pxW == b.pxW && a.pxH == b.pxH && a.dpiX == b.dpiX && a.dpiY == b.dpiY &&
    a.bitDepth == b.bitDepth && a.orientation == b.orientation && a.color == b.color &&
    a.filter == b.filter && a.alpha == b.alpha && a.recoded == b.recoded &&
    a.losses == b.losses && a.data == b.data && a.form.isNone && b.form.isNone

/-- Persisted bytes retain their meaning; malformed tags, counts, truncations
and trailing bytes are cache misses. The universal identity is proved in Image;
these checks additionally exercise the executable byte primitives. -/
def imageCodecChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, plan, encoded) in
      [("profile and soft mask", profiledPlan, profiledBytes),
       ("palette and color key", indexedPlan, indexedBytes)] do
    t s!"image codec: exact LTIMG3 bytes ({name})" (Image.encodeBin plan == encoded)
    t s!"image codec: decode persisted LTIMG3 bytes ({name})"
      ((Image.decodeBin encoded).any (sameRaster plan))
    t s!"image codec: every strict prefix refuses ({name})"
      ((List.range encoded.size).all fun n => (Image.decodeBin (encoded.extract 0 n)).isNone)
    t s!"image codec: trailing bytes refuse ({name})"
      ((Image.decodeBin (encoded ++ bytes [0, 255])).isNone)
  for pos in [0, 5, 6, 7, 8, 66] do
    t s!"image codec: invalid magic or tag refuses at {pos}"
      ((Image.decodeBin (profiledBytes.set! pos 255)).isNone)
  -- LTIMG3's palette/profile/key/plane/data/loss lengths are u32s at these
  -- offsets. An oversized count must refuse before allocation or traversal.
  for pos in [38, 42, 46, 54, 58, 62] do
    let oversized := (List.range 4).foldl
      (fun b k => b.set! (pos + k) 255) profiledBytes
    t s!"image codec: truncated declared extent refuses at {pos}"
      ((Image.decodeBin oversized).isNone)
  -- Empty variants and the largest representable integers need no giant
  -- allocation: payload lengths are separate from the scalar fields.
  let empty : Image.Plan :=
    { pxW := 0, pxH := 0, dpiX := 0, dpiY := 0, bitDepth := 0, orientation := 0
      data := .empty }
  let edge : Image.Plan :=
    { empty with
      pxW := 4294967295, pxH := 4294967295, dpiX := 4294967295, dpiY := 4294967295
      bitDepth := 4294967295, orientation := 4294967295 }
  for seed in [empty, edge] do
    for color in [Image.ColorSpaceDecl.gray, .rgb, .indexed .empty,
        .iccBased 0 .empty, .iccBased 4294967295 .empty] do
      for alpha in [Image.Alpha.opaque, .colorKey #[],
          .colorKey #[0, 4294967295], .soft .empty 0, .soft .empty 4294967295] do
        let p := { seed with color, alpha }
        t "image codec: empty fields and u32 boundary retain every field"
          ((Image.decodeBin (Image.encodeBin p)).any (sameRaster p))
  -- A value outside the theorem's domain truncates as the existing format
  -- always has; no runtime certification is added to the encoder.
  let tooWide := { empty with pxW := 4294967296 }
  t "image codec: u32 representability bound is necessary"
    ((Image.decodeBin (Image.encodeBin tooWide)).any fun p =>
      p.pxW == 0 && p.pxW != tooWide.pxW)
