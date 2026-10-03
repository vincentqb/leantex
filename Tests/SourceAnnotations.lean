import LeanTex.Core.Ir
import LeanTex.Core.Struct
import LeanTex.Core.Contrast
import LeanTex.Core.MarkdownDoc
import LeanTex.Core.HtmlDoc

open LeanTex.Core LeanTex.Core.Ir

namespace Tests

private def annotationCheck (ref : IO.Ref (List String)) (name : String)
    (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

/-- Put the same content in body, caption, picture, and furniture regions.
The expected document is built independently with source-free content. -/
private def annotationDoc (xs : Array Inline) (source : Option Span) : Doc :=
  { head := some xs, foot := some xs, logo := some xs
    headline := some { title := xs, author := xs, institute := xs }
    logoLeft := some xs, logoRight := some xs
    styles := { entries := #[("titlepage", {
      font := some xs, authorFont := some xs, marker := some xs
      slots := #[{ parts := #[{ datum := none, content := xs, font := some xs }] }] })] }
    body := #[
      .para xs,
      .section 1 false none xs,
      .equation xs xs,
      .list false #[#[.para xs]],
      .frame xs false .top false #[.para xs, .framefoot xs],
      .float .figure (some 1) false #[.para xs] xs,
      .table #[{ width := .natural, align := .left }] true true #[#[xs]] #[] #[],
      .algorithm false false #[{
        depth := 0, kind := .statement, content := xs, comment := some xs }],
      .bibliography "invented" none #[{ key := "entry", marker := none, content := xs }],
      .verbatim none "first\nsecond" { source := source, caption := some (1, xs) },
      .picture { shapes := #[.label 0 0 xs { r := 20, g := 30, b := 40 } 1000 .center] }] }

/-- Locations carry diagnostic provenance without adding a semantic leaf,
changing backend structure, or stopping a generic traversal. Erasure rejoins
adjacent text inside each semantic region and clears listing provenance.
The author-font case fails before the generic furniture map includes it.
These checks can run without the elaborator or layout integration suite. -/
def sourceAnnotationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := annotationCheck ref
  let span : Span := { file := "invented.tex", pos := { line := 3, col := 5 } }
  let annotated : Array Inline := #[
    .text "a", .located span #[], .located span #[.text "b",
      .located span #[.text "c"]], .text "d"]
  let bare : Array Inline := #[.text "abcd"]
  t "source annotations: nested erasure rejoins adjacent text"
    (Ir.eraseLocationInlines annotated == bare)
  t "source annotations: a generic identity map retains provenance"
    (Ir.mapInlines id annotated == annotated)
  t "source annotations: empty locations are not template holes"
    (Ir.fillTemplate #[.located span #[]] bare == #[.located span #[]])
  let ink : Ir.Color := { r := 20, g := 30, b := 40 }
  let wrappers : Array (String × (Array Inline → Inline)) := #[
    ("style", Inline.styled .bold), ("color", Inline.colored ink none),
    ("role", Inline.role "accent"), ("link", Inline.link "https://example.invalid"),
    ("decoration", Inline.decorated .underline),
    ("overlay", Inline.onSteps ⟨2, some 4, []⟩),
    ("footnote", Inline.footnote (some 1))]
  for (name, wrap) in wrappers do
    let xs := #[.text "left", .located span #[wrap annotated], .text "right"]
    t s!"source annotations: recursive erasure preserves {name} boundaries"
      (Ir.eraseLocationInlines xs == #[.text "left", wrap bare, .text "right"])
  t "source annotations: both overlay alternatives are erased in order"
    (Ir.eraseLocationInlines #[.altSteps ⟨2, some 4, []⟩ annotated
      #[.located span #[.text "other"], .text " page"]] ==
      #[.altSteps ⟨2, some 4, []⟩ bare #[.text "other page"]])
  let doc := annotationDoc annotated (some span)
  let expected := annotationDoc bare none
  t "source annotations: body, listing, picture, and furniture erasure"
    (Ir.eraseLocations doc == expected)
  t "source annotations: erasure is idempotent across document regions"
    (Ir.eraseLocations (Ir.eraseLocations doc) == Ir.eraseLocations doc)
  let content : Array Inline := #[
    .styled .bold #[.text "bold"], .colored ink none #[.text "color"],
    .onSteps ⟨2, some 4, []⟩ #[.text "overlay"],
    .footnote (some 7) #[.text "note"]]
  let located : Array Inline := #[.located span content]
  t "source annotations: no additional semantic leaves"
    (Struct.leafCountInlines located == Struct.leafCountInlines content)
  t "source annotations: overlay extent traverses locations"
    (Ir.maxStepInlines located == 4 && Ir.maxStepInlines located == Ir.maxStepInlines content)
  t "source annotations: footnotes traverse locations"
    (Ir.footnotesOf #[.para located] == Ir.footnotesOf #[.para content])
  t "source annotations: contrast reads the same colors"
    (Contrast.judgedPairs { body := #[.para located] } ==
      Contrast.judgedPairs { body := #[.para content] })
  t "source annotations: Markdown emits the body unchanged"
    (MarkdownDoc.inlineText located == MarkdownDoc.inlineText content)
  t "source annotations: Markdown listing source is invisible"
    (MarkdownDoc.emit doc == MarkdownDoc.emit expected)
  let marker : Array Inline := #[.styled .bold bare]
  t "source annotations: whole-marker style survives separate location groups"
    (HtmlDoc.markerCss? #[.located span marker,
      .located span #[.italicCorr false], .located span #[]] == HtmlDoc.markerCss? marker)
  let label := fun xs =>
    Html.render (Html.elem "text" (HtmlDoc.labelNodesList {} #[] xs.toList)) 0
  t "source annotations: SVG labels gain no wrapper"
    (label #[.located span #[.text "label"]] == label #[.text "label"])
  let emit := fun body => (HtmlDoc.emit { css := .none } { body := body }).1
  t "source annotations: HTML paragraphs gain no wrapper"
    (emit #[.para located] == emit #[.para content])
  t "source annotations: HTML display classification sees the body"
    (emit #[.center #[.para #[.located span #[.math true "x"]]]] ==
      emit #[.center #[.para #[.math true "x"]]])
  let description : Array Inline := #[
    .role Ir.descLabelRole #[.text "Term"], .text "Definition"]
  t "source annotations: HTML description classification sees the body"
    (emit #[.list false #[#[.para #[.located span description]]]] ==
      emit #[.list false #[#[.para description]]])
  let row : Array Inline := #[.text "left", .fill, .text "right"]
  t "source annotations: HTML fill classification sees the body"
    (emit #[.para #[.located span row]] == emit #[.para row])
  t "source annotations: HTML listing source is invisible"
    (emit #[.verbatim none "first\nsecond" { source := some span }] ==
      emit #[.verbatim none "first\nsecond" {}])

end Tests
