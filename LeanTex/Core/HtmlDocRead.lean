module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.HtmlReadProof
public import LeanTex.Core.HtmlScripts

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

/-- What the HTML parser finds a page runs, none where the page does not parse. -/
@[expose] public def scripts (page : String) : List HtmlRead.Run :=
  ((HtmlRead.parse page).map HtmlRead.Dom.runs).getD []

/-- No published page whose tree reads as a stack runs anything (`HtmlRead.Run`) but the deck's
constant script or the renderer the run declares, white space at its ends aside. -/
public theorem emit_scripts_mem {r : Option String} (page : ClosedPage r)
    (h : Html.DocOk page.lang page.head page.body = true) :
    (HtmlRead.parse page.render).isSome ∧ ∀ x ∈ scripts page.render,
      x = .script (HtmlRead.trimWs deckScript.toList) ∨
        ∃ js, r = some js ∧ x = .script (HtmlRead.trimWs js.toList) := by
  obtain ⟨d, hd, hr⟩ := HtmlResource.ClosedPage.runs_admitted page h
  refine ⟨by simp [hd], ?_⟩
  intro x hx
  simp only [scripts, hd, Option.map_some, Option.getD_some] at hx
  obtain ⟨js, hjs, rfl⟩ := hr x hx
  simp only [admittedScripts, Array.mem_append, Array.mem_singleton, Option.mem_toArray] at hjs
  rcases hjs with rfl | hjs
  · exact Or.inl rfl
  · exact Or.inr ⟨js, hjs, rfl⟩

/-- What the page publication ships runs, its tree reading as a stack: the deck's constant script
and the declared renderer alone (`emit_scripts_mem`). -/
public theorem emitClosed_scripts_mem (cfg : Config) (doc : Ir.Doc) (svgChecked : Array ByteArray)
    {page : ClosedPage cfg.mathRenderer} (hp : (emitClosed cfg doc svgChecked).1 = .ok page)
    (h : Html.DocOk (doc.info.language.getD "en") (emitTree cfg doc).1 (emitTree cfg doc).2.1 = true) :
    page.render = (emit cfg doc).1 ∧ ∀ x ∈ scripts (emit cfg doc).1,
      x = .script (HtmlRead.trimWs deckScript.toList) ∨
        ∃ js, cfg.mathRenderer = some js ∧ x = .script (HtmlRead.trimWs js.toList) := by
  have hr := (emitClosed_covers cfg doc svgChecked hp).1
  obtain ⟨hl, hh, hb⟩ := emitClosed_fields cfg doc svgChecked hp
  refine ⟨hr, ?_⟩
  rw [← hr]
  exact (emit_scripts_mem page (by rw [hl, hh, hb]; exact h)).2

end LeanTex.Core.HtmlDoc
