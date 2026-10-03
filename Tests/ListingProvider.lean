import Tests.ShellHighlight
import LeanTex.Cli.DriverDiag

open LeanTex.Core LeanTex.Cli

namespace Tests.ListingProvider

-- Synthetic classification data, independent of an installed lexer. The
-- provider's language accuracy is a separate rendered acceptance report.
def providerSource : String := "echo\t\"ready\"\n\n$HOME"

def reply (request : ListingReply.Request) : String :=
  ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson request #[
    ShellHighlight.shellTokenJson 0 "Token.Name.Builtin" "echo",
    ShellHighlight.shellTokenJson 4 "Token.Text" "\t",
    ShellHighlight.shellTokenJson 5 "Token.Literal.String.Double" "\"ready\"",
    ShellHighlight.shellTokenJson 12 "Token.Text" "\n\n",
    ShellHighlight.shellTokenJson 14 "Token.Name.Variable" "$HOME"]]

def prepared (markdown : Bool) (input : String) : Elab.Prepared × Array Diag :=
  let (raws, ds) := if markdown then Md.read "listing.md" input else
    let (toks, ld) := Lex.lex "listing.tex" input
    let (raws, pd) := Parse.parse "listing.tex" toks
    (raws, ld ++ pd)
  (Elab.prepare "listing" raws, ds)

end Tests.ListingProvider

namespace Tests

/-- Checked replies must reach real frontend listings and both artifacts.
Missing, stale and forged replies keep the exact source without class paint;
completed refusals retain their typed, keyed diagnostic on re-elaboration. -/
def listingProviderChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some bytes ← findFont | failures ref "listing provider: fixture font missing"
  let .ok font := Font.parse bytes | failures ref "listing provider: fixture font invalid"
  let fonts := oneFaceOf font
  let source := ListingProvider.providerSource
  let cases := [
    (false, Ir.ListingStyle.default, dvDoc "\\usepackage{minted}"
      ("\\begin{minted}{bash}\n" ++ source ++ "\n\\end{minted}")),
    (false, Ir.ListingStyle.friendly, dvDoc "\\usepackage{minted}\\setminted{style=friendly}"
      ("\\begin{minted}{sh}\n" ++ source ++ "\n\\end{minted}")),
    (false, Ir.ListingStyle.default, dvDoc "\\usepackage{listings}"
      ("\\begin{lstlisting}[language=shell]\n" ++ source ++ "\n\\end{lstlisting}")),
    (true, Ir.ListingStyle.default, "```bash\n" ++ source ++ "\n```")]
  for (markdown, style, input) in cases do
    let (base, earlier) := ListingProvider.prepared markdown input
    let (cold, coldDiags, _) := Elab.runPrepared "listing" base earlier
    let requests := ListingReply.requests cold
    t "listing provider: settled frontend produces one exact request"
      (coldDiags.all (·.severity != .error) && requests.size == 1 &&
        requests.all (·.source == source))
    let some request := requests[0]? | failures ref "listing provider: request missing"
    let .ok (answers, errors) := ListingReply.decode requests (ListingProvider.reply request)
      | failures ref "listing provider: synthetic reply rejected"
    t "listing provider: complete classification has no refusal" errors.isEmpty
    let snapshot := { base with listingReplies := answers }
    let (doc, ds, _) := Elab.runPrepared "listing" snapshot earlier
    let entries := ListingHighlight.listings doc
    t "listing provider: snapshot preserves source and selected style"
      (ds.all (·.severity != .error) && entries.size == 1 && entries.all fun (_, text, spec) =>
        Ir.verbatimLines text == request.lines && spec.style == style &&
        (spec.tokenLines text).map LeanTex.Core.ListingHighlight.lineText == request.lines)
    let (_, body, _) := HtmlDoc.emitTree {} doc
    let codes := ListingHighlight.codeNodesList #[] body.toList
    t "listing provider: typed HTML preserves tabs and blank lines"
      (codes.size == 1 && codes.all fun code => nodeTextOne "" code == source)
    let out := layoutOf fonts doc
    let glyphs := ListingHighlight.glyphColors out
    t "listing provider: shipped PDF glyph order preserves the source"
      ((glyphs.filter fun (c, _) => ShellHighlight.visible c).map (·.1) ==
        ShellHighlight.visibleText source)
    let painted := ShellHighlight.htmlPaintList none #[] codes.toList
    let pdf := pdfText (Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info)
    for (word, kind) in [("echo", LeanTex.Core.ListingHighlight.Kind.builtin),
        ("ready", .string), ("$HOME", .name)] do
      let ink := (Listing.ink doc.palette none kind (style := style)).getD Ir.Color.black
      t "listing provider: Layout.Out ships checked class ink"
        ((ShellHighlight.witnessPaint? source word glyphs).any fun colors =>
          !colors.isEmpty && colors.all (· == ink))
      t "listing provider: emitted PDF contains checked class paint"
        (bytesContain pdf ink.pdfFill)
      t "listing provider: typed HTML agrees with shipped glyph ink"
        ((ShellHighlight.witnessPaint? source word painted).any fun colors =>
          !colors.isEmpty && colors.all fun color =>
            color.any fun css => hasStr css (HtmlDoc.cssColor ink))
    let forged := answers.map fun a => { a with tokens := #[#[{ text := "changed" }]] }
    let stale := answers.map fun a => { a with request := { a.request with source := "stale" } }
    for rejected in [#[], forged, stale] do
      let (plain, _, _) := Elab.runPrepared "listing" { base with listingReplies := rejected } earlier
      let (_, plainBody, _) := HtmlDoc.emitTree {} plain
      let (_, coldBody, _) := HtmlDoc.emitTree {} cold
      t "listing provider: missing, stale and forged answers ship the original plain page"
        (plainBody.map (Html.render · 0) == coldBody.map (Html.render · 0) &&
          reprStr (layoutOf fonts plain).pages == reprStr (layoutOf fonts cold).pages)
    let .ok (plainReplies, refused) := ListingReply.decode requests
        (ShellHighlight.shellBatchJson #[ShellHighlight.shellFailureJson request "unsupported"])
      | failures ref "listing provider: completed refusal rejected"
    let warnings := refused.map fun (r, failure) =>
      DriverDiag.listingHighlightUnavailable r.language failure.reason
    let rejected := { base with listingReplies := plainReplies }
    let (plain, first, _) := Elab.runPrepared "listing" rejected (earlier ++ warnings)
    let (_, replay, _) := Elab.runPrepared "listing" rejected (earlier ++ warnings)
    t "listing provider: completed refusal keeps source and replays one keyed warning"
      (first.filter (·.code == "W0393") == warnings &&
        replay.filter (·.code == "W0393") == warnings &&
        warnings.all (·.subject == some ("listing-language:" ++ request.language)) &&
        reprStr (layoutOf fonts plain).pages == reprStr (layoutOf fonts cold).pages)

end Tests
