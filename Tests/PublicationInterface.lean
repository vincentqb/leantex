module

import LeanTex.Cli.Publication

/-! Ordinary publishers carry the checked HTML witness and typed diagnostics. -/

open LeanTex.Core LeanTex.Cli LeanTex.Cli.Publication

namespace Tests.PublicationInterface

example : String → HtmlDoc.Config → Ir.Doc → IO (Except String HtmlDoc.Config) :=
  captureHtmlResources
example (renderer : Option String) : HtmlDoc.ClosedPage renderer → HtmlArtifact :=
  HtmlArtifact.ofPage
example : String → HtmlDoc.Config → Ir.Doc →
    IO (Except String HtmlArtifact × Array Diag) := prepareHtml
example : Option String → Option (String × HtmlArtifact) →
    Option (String × String) → Option (String × ByteArray) → IO (Array String × Array Diag) :=
  publish
example (renderer : Option String) (page : HtmlDoc.ClosedPage renderer) : HtmlArtifact :=
  { render := page.render, renderer, render_exact := ⟨page, rfl⟩ }
example (artifact : HtmlArtifact) : String := artifact.render
example (artifact : HtmlArtifact) :
    ∃ page : HtmlDoc.ClosedPage artifact.renderer, artifact.render = page.render :=
  artifact.render_exact

example : Array HtmlResource.Embedded → Array ByteArray → Except String (Array ByteArray) :=
  fun resources checked => attestSvg resources checked

example : True := by
  fail_if_success have := LeanTex.Cli.Publication.htmlLocalBytes
  trivial

end Tests.PublicationInterface
