module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.HtmlReadProof

/-! The page the HTML backend writes, read back by the HTML Standard's parser. -/

namespace LeanTex.Core.HtmlDoc

/-- The page `emit` writes parses to its emitted tree, with the renderer's white space as text,
whenever that tree reads as a stack (`Html.DocOk`, which every corpus page meets). -/
public theorem emit_parse_exact (cfg : Config) (doc : Ir.Doc)
    (h : Html.DocOk (doc.info.language.getD "en") (emitTree cfg doc).1 (emitTree cfg doc).2.1 = true) :
    HtmlRead.parse (emit cfg doc).1 =
      some (Html.fDoc (doc.info.language.getD "en") (emitTree cfg doc).1 (emitTree cfg doc).2.1) := by
  rw [emit_tree_exact]
  exact Html.parse_render_exact _ _ _ h

/-- The text of the page `emit` writes, white space aside, is what the emitted body's text nodes
hold outside style sheets and scripts, whenever the tree reads as a stack. -/
public theorem emit_pageText_ink (cfg : Config) (doc : Ir.Doc)
    (h : Html.DocOk (doc.info.language.getD "en") (emitTree cfg doc).1 (emitTree cfg doc).2.1 = true) :
    ∃ t, HtmlRead.pageText (emit cfg doc).1 = some t ∧
      t.toList.filter Html.inked = (Html.Node.inkList (emitTree cfg doc).2.1.toList).filter Html.inked := by
  rw [emit_tree_exact]
  exact Html.pageText_render_ink _ _ _ h

end LeanTex.Core.HtmlDoc
