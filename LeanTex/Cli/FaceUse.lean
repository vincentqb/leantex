module

public import LeanTex.Core.Font
public import LeanTex.Core.UnusedSetting

/-! A face the document declares that no text is set in, named as W0449 over the settled face set:
no content slot resolves to it, and no glyph another face lacks falls back to it. -/

namespace LeanTex.Cli.FaceUse

open LeanTex.Core

/-- The fonts a declared face's family is loaded as: the slots its declaration resolves, as the
face set's assembly reads them, or the math face. -/
public def ownFonts (fs : Font.FontSet) (doc : Ir.Doc) (key : String) : Array Nat :=
  let slot (s : Nat) : Array Nat := fs.index.filterMap fun ((t, _, _), i) =>
    if t == s then some i else none
  let spec := doc.fonts
  let slides := doc.docClass == .slides
  match key with
  | "mono" => slot 2
  | "sans" => slot 1 ++ (if slides || spec.body.isNone then slot 0 else #[])
  | "body" =>
    (if slides && spec.sans.isSome then #[] else slot 0) ++
      (if spec.sans.isNone then slot 1 else #[]) ++ (if spec.mono.isNone then slot 2 else #[])
  | "math" => fs.math.toArray
  | k =>
    if k.startsWith "family." then
      ((spec.familySlot (k.drop "family.".length).toString).map slot).getD #[]
    else #[]

/-- Whether some glyph of the document is set from one of these fonts as the first face that has
it, which a run in another face falls back to. -/
public def servesFallback (fs : Font.FontSet) (own : Array Nat) : Bool :=
  fs.fallback.any fun (_, i) => own.contains i

/-- The W0449 of each declared face no content slot resolves to and no fallback glyph reads. -/
public def diags (faces : Array (String × Span)) (fs : Font.FontSet) (doc : Ir.Doc) :
    Array Diag :=
  if faces.isEmpty then #[] else
  let shown := UnusedSetting.shown doc
  let slides := doc.docClass == .slides
  faces.filterMap fun (key, span) =>
    if UnusedSetting.faceUsed doc.fonts slides shown key || servesFallback fs (ownFonts fs doc key)
    then none else some (UnusedSetting.faceDiag key span)

end LeanTex.Cli.FaceUse
