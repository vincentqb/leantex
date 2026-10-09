module

import LeanTex.Cli.Publication

/-! Ordinary publishers carry the checked HTML witness and typed diagnostics.
Local resource capture details are not part of the public boundary. -/

open LeanTex.Core LeanTex.Cli LeanTex.Cli.Publication

namespace Tests.PublicationInterface

example : String → HtmlDoc.Config → Ir.Doc → IO (Except String HtmlDoc.Config) :=
  captureHtmlResources
example : HtmlDoc.ClosedPage → HtmlArtifact := HtmlArtifact.ofPage
example : String → HtmlDoc.Config → Ir.Doc →
    IO (Except String HtmlArtifact × Array Diag) := prepareHtml
example : Option String → Option (String × HtmlArtifact) →
    Option (String × String) → Option (String × ByteArray) → IO (Array String) :=
  publish
example (page : HtmlDoc.ClosedPage) : HtmlArtifact :=
  { render := page.render, render_exact := ⟨page, rfl⟩ }
example (artifact : HtmlArtifact) : String := artifact.render
example (artifact : HtmlArtifact) :
    ∃ page : HtmlDoc.ClosedPage, artifact.render = page.render :=
  artifact.render_exact

example : PicCache.Outcome → Verdict := svgVerdict
example (o : PicCache.Outcome) : svgVerdict o = .refuse ↔ ∃ w, o = .refused w :=
  svgVerdict_refuse_exact o
example (o : PicCache.Outcome) : svgVerdict o = .omit ↔ ∃ w, o = .inconclusive w :=
  svgVerdict_omit_exact o
example : Array (ByteArray × String) → HtmlResource.Embedded → Option String := omittedWhy
example : Array (ByteArray × String) → Image.Loaded → Option String := omittedFace
example : Array (ByteArray × String) → HtmlDoc.Config → Ir.Doc →
    HtmlDoc.Config × Ir.Doc × Array Diag := omitFaces
example (cfg : HtmlDoc.Config) (doc : Ir.Doc) : omitFaces #[] cfg doc = (cfg, doc, #[]) :=
  omitFaces_id cfg doc
example (omitted : Array (ByteArray × String)) (cfg : HtmlDoc.Config) (doc : Ir.Doc) (k : Nat)
    (en : Image.Loaded) (why : String) (h : cfg.imgs.get? k = some en)
    (hwhy : omittedFace omitted en = some why) :
    (omitFaces omitted cfg doc).1.imgs.get? k = some { en with webError := some why } ∧
      (en.src.startsWith Ir.picSrcPrefix = true →
        ∃ d ∈ (omitFaces omitted cfg doc).2.2, d.kind = .W0378 ∧ d.subject = some en.src) :=
  omitFaces_named omitted cfg doc k en why h hwhy
example (omitted : Array (ByteArray × String)) (cfg : HtmlDoc.Config) (doc : Ir.Doc) (k : Nat)
    (en : Image.Loaded) (h : cfg.imgs.get? k = some en) (hkept : omittedFace omitted en = none) :
    (omitFaces omitted cfg doc).1.imgs.get? k = some en :=
  omitFaces_kept_exact omitted cfg doc k en h hkept
example (omitted : Array (ByteArray × String)) (cfg : HtmlDoc.Config) (doc : Ir.Doc)
    (name : String) (icon : HtmlResource.Embedded) (h : cfg.favicon = some (name, icon))
    (hgone : (omitFaces omitted cfg doc).1.favicon = none) :
    (omitFaces omitted cfg doc).2.1.info.favicon = none ∧
      ∃ d ∈ (omitFaces omitted cfg doc).2.2, d.kind = .W0605 ∧ d.subject = some name :=
  omitFaces_icon_named omitted cfg doc name icon h hgone

example : True := by
  fail_if_success have := LeanTex.Cli.Publication.htmlLocalBytes
  fail_if_success have := LeanTex.Cli.Publication.said
  fail_if_success have := LeanTex.Cli.Publication.omitEntry
  trivial

end Tests.PublicationInterface
