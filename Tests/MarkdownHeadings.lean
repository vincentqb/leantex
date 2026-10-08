import Tests.Support
import LeanTex.Core.MarkdownDoc

open LeanTex.Core

namespace MarkdownHeadings

/-- Both artifacts and the Markdown twin project one bounded IR rank.
The actual emitted HTML tree and PDF roles are read back below. -/
theorem heading_artifacts_agree (level : Ir.HeadingLevel) :
    HtmlDoc.headingTag level = "h" ++ toString (Ir.headingRank level) ∧
    Pdf.headingTag level = "H" ++ toString (Ir.headingRank level) ∧
    (MarkdownDoc.headingMarker level).toList =
      List.replicate (Ir.headingRank level) '#' := by
  refine ⟨rfl, Pdf.heading_type_projects level, ?_⟩
  simp [MarkdownDoc.headingMarker]

/-- Serialization cannot emit an empty or seven-hash heading marker. This
is the IR rank bound projected through the serializer, not a sample. -/
theorem heading_marker_between (level : Ir.HeadingLevel) :
    1 ≤ (MarkdownDoc.headingMarker level).toList.length ∧
      (MarkdownDoc.headingMarker level).toList.length ≤ 6 := by
  simpa [MarkdownDoc.headingMarker] using Ir.headingRank_between level

/-- Invented, short enough that every heading and its following paragraph
fit on one page. The rank oracle is the source's literal hash count. -/
def source : String :=
  "# Amber\n\nFirst body.\n\n## Birch\n\nSecond body.\n\n### Cedar\n\nThird body.\n\n\
#### Dogwood\n\nFourth body.\n\n##### Elm\n\nFifth body.\n\n###### Fir\n\nSixth body.\n"

def titles : Array String := #["Amber", "Birch", "Cedar", "Dogwood", "Elm", "Fir"]

def tags : Array String := #["h1", "h2", "h3", "h4", "h5", "h6"]

def headings (doc : Ir.Doc) : Array (String × String) :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  (elemNodesList (tags.contains ·) #[] body.toList).filterMap fun n =>
    match n with
    | .elem tag _ kids => some (tag, nodeTextList "" kids.toList)
    | _ => none

end MarkdownHeadings

/-- Rank and text are checked on the shipped HTML tree, the layout, and
the serialized PDF structure. A title is independently tested alongside
all six body ranks; it cannot consume a rank and turn the last into H7. -/
def markdownHeadingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabMd MarkdownHeadings.source
  let expected := MarkdownHeadings.tags.zip MarkdownHeadings.titles
  t "all six Markdown heading ranks and titles reach the HTML tree"
    (MarkdownHeadings.headings doc == expected)
  t "supported heading depth has no degraded or unknown-option route"
    (!ds.any (fun d => d.subject == some "md:heading-depth" || d.kind == .W0110))
  let titled := { doc with
    body := #[Ir.Block.section 0 true none #[.text "Document title"]] ++ doc.body }
  t "a document title and six body ranks coexist without consuming a rank"
    (MarkdownHeadings.headings titled == #[("h1", "Document title")] ++ expected)
  let (_, titledBody, _) := HtmlDoc.emitTree {} titled
  t "the artifact never invents an h7"
    ((elemNodesList (· == "h7") #[] titledBody.toList).isEmpty)
  let exported := MarkdownDoc.emit doc
  for (rank, title) in (List.range 6).zip MarkdownHeadings.titles.toList do
    let marker := String.ofList (List.replicate (rank + 1) '#')
    t s!"Markdown serialization preserves the rank of {title}"
      ((exported.splitOn "\n").contains (marker ++ " " ++ title))
  let titledLines := (MarkdownDoc.emit titled).splitOn "\n"
  t "the Markdown twin keeps title and body h1 separate without shifting h6"
    ((titledLines.filter (·.startsWith "# ")) == ["# Document title", "# Amber"]
      && titledLines.contains "###### Fir"
      && !titledLines.any (·.startsWith "####### "))
  t "seven hashes stay ordinary paragraph text"
    (MarkdownHeadings.headings (elabMd "####### Not a heading\n").1 == #[]
      && hasStr (mdTreeOf "####### Not a heading\n") "<p>####### Not a heading</p>")
  t "a later level-one Markdown heading is not a misplaced document title"
    (!(dvMd "# First\n\n## Child\n\n# Second\n").any (·.kind == .W0321)
      && MarkdownHeadings.headings (elabMd "# First\n\n## Child\n\n# Second\n").1 ==
        #[("h1", "First"), ("h2", "Child"), ("h1", "Second")])
  for src in ["> ###### Quoted\n", "- ###### Listed\n"] do
    t "a nested heading retains its sixth level"
      (MarkdownHeadings.headings (elabMd src).1 ==
        #[("h6", if src.startsWith ">" then "Quoted" else "Listed")])
  let escaped := "###### &lt;script&gt; \\textbf{literal} &amp; *kept*\n"
  let (_, escapedBody, _) := HtmlDoc.emitTree {} (elabMd escaped).1
  let rendered := Html.render (Html.elem "div" escapedBody) 0
  t "heading text stays escaped and Markdown emphasis stays typed"
    (hasStr rendered "&lt;script&gt;" && hasStr rendered "\\textbf{literal}"
      && hasStr rendered "&amp;" && hasStr rendered "<em>kept</em>"
      && (elemNodesList (· == "script") #[] escapedBody.toList).isEmpty)
  let native := (elabStr (dvDoc "" "\\section{Native}\n\
\\paragraph{Run in} Tail.\\subparagraph{Nested run in} End.")).1
  t "native sections keep their rank and paragraph commands remain run in"
    ((MarkdownHeadings.headings native).map Prod.fst == #["h2"]
      && hasStr (mdFlatten "" (HtmlDoc.emitTree {} native).2.1.toList)
        "<strong>Run in</strong>"
      && hasStr (mdFlatten "" (HtmlDoc.emitTree {} native).2.1.toList)
        "<strong>Nested run in</strong>")
  let some fonts ← serifFacesSet
    | t "the Markdown heading regression faces load" false
      return
  let out := layoutOf fonts doc
  let lines := (bodyLines out).map lineText
  t "all six heading titles ship once and in order on the PDF layout"
    (lines.filter (MarkdownHeadings.titles.contains ·) == MarkdownHeadings.titles)
  for (d, expectedRoles) in
      [(doc, #["H1", "H2", "H3", "H4", "H5", "H6"]),
       (titled, #["H1", "H1", "H2", "H3", "H4", "H5", "H6"])] do
    let laid := layoutOf fonts d
    let pdf := Pdf.write (Layout.Geom.ofPage d.page) fonts laid.pages d.info {}
      laid.outline (tree := Struct.ofDoc (Layout.pdfView d))
    match PdfRead.objects pdf with
    | .error _ => t "the six-heading PDF parses" false
    | .ok entries =>
      let roles := entries.val.filterMap fun e =>
        match e.val.get? "S" with
        | some (.name s) =>
          if s.startsWith "H" && (s.drop 1).toString.toNat?.isSome then some s else none
        | _ => none
      t "the PDF file carries exactly the heading structure roles in order"
        (roles == expectedRoles)
