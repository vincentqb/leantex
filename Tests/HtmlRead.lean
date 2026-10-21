module

public import Tests.Support
public import LeanTex.Core.HtmlReadProof

public section

open LeanTex.Core

namespace Tests

/-- Every corpus page's head and body read back as the stack builder they are, so the parser's
reading of the page is its rendered tree (`Html.parse_render_exact`); the reading refuses what the
standard's builder would repair, and a preformatted block keeps a leading line end. -/
def htmlReadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut pages := 0
  for name in goldenNames do
    let (doc, _) ← goldenDoc name
    for mode in [HtmlDoc.CssMode.own, .bulma, .none] do
      let (head, body, _) := HtmlDoc.emitTree { css := mode } doc
      let lang := doc.info.language.getD "en"
      t s!"html read: {name} {repr mode}: the page reads back as its rendered tree"
        (Html.DocOk lang head body)
      pages := pages + 1
  t s!"html read: the corpus is read ({pages} pages)" (0 < pages)
  let page (body : Array Html.Node) := Html.document "en" #[] body
  let reads (body : Array Html.Node) := (HtmlRead.parse (page body)).isSome
  t "html read: a paragraph inside a paragraph is repaired by the standard, outside the reading"
    (!Html.DocOk "en" #[] #[Html.elem "p" #[Html.elem "p" #[Html.text "x"]]] &&
      !reads #[Html.elem "p" #[Html.elem "div" #[Html.text "x"]]])
  t "html read: a list item directly inside a list item is outside the reading"
    (!Html.DocOk "en" #[] #[Html.elem "ul" #[Html.elem "li" #[Html.elem "li" #[]]]])
  t "html read: a row directly inside a table, which the standard wraps in a body, is outside it"
    (!Html.DocOk "en" #[] #[Html.elem "table" #[Html.elem "tr" #[Html.elem "td" #[]]]] &&
      !reads #[Html.elem "table" #[Html.elem "tr" #[Html.elem "td" #[]]]])
  t "html read: a void element with children is outside the reading"
    (!Html.DocOk "en" #[] #[Html.elem "img" #[Html.text "lost"]])
  t "html read: text in a table, which the standard moves before it, is outside the reading"
    (!reads #[Html.elem "table" #[Html.text "moved"]])
  t "html read: a block inside SVG text breaks out under the standard, outside the reading"
    (!reads #[Html.elem "svg" #[Html.elem "text" #[Html.elem "div" #[]]]])
  t "html read: a preformatted block opening with a line end keeps it in the page's text"
    (HtmlRead.pageText (page #[Html.elem "pre" #[Html.text "\nfirst"]]) ==
      some "\n    \nfirst\n  \n\n")
  t "html read: a preformatted block opening with text reads as written"
    (HtmlRead.pageText (page #[Html.elem "pre" #[Html.text "first"]]) == some "\n    first\n  \n\n")
  t "html read: escaped text and attributes read back as written"
    (HtmlRead.parse (page #[Html.elem "a" #[Html.text "a<b & \"c\""] #[("title", "q\"'<&>")]]) ==
      some (Html.fDoc "en" #[] #[Html.elem "a" #[Html.text "a<b & \"c\""] #[("title", "q\"'<&>")]]))
  t "html read: a style sheet in a column group, which the standard moves out, is outside the reading"
    (!reads #[Html.elem "table" #[Html.elem "colgroup" #[Html.Node.style "a{}", Html.elem "col" #[]]]] &&
      reads #[Html.elem "table" #[Html.Node.style "a{}", Html.elem "tbody" #[Html.elem "tr" #[Html.elem "td" #[]]]]])
  t "html read: a style sheet holding its own end tag is removed whole, the page still read"
    (reads #[Html.Node.style "a{}</style><p>x"])

end Tests
