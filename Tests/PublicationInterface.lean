module

import LeanTex.Cli.Publication

/-! Ordinary publishers carry the checked HTML witness and typed diagnostics.
Local resource capture details are not part of the public boundary. -/

open LeanTex.Core LeanTex.Cli.Publication

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

example : True := by
  fail_if_success have := LeanTex.Cli.Publication.htmlLocalBytes
  trivial

end Tests.PublicationInterface
