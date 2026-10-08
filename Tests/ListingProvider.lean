import Tests.ShellHighlight
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.ListingHighlight
import LeanTex.Cli.RunBounded
import LeanTex.Cli.ToolProbe

open LeanTex.Core LeanTex.Cli

namespace Tests.ListingProvider

-- Synthetic classification data, independent of an installed lexer. The
-- provider's language accuracy is a separate rendered acceptance report.
def providerSource : String := "echo\t\"ready\"\n\n$HOME  # terminal\t  "

def reply (request : ListingReply.Request) : String :=
  ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson request #[
    ShellHighlight.shellTokenJson 0 "Token.Name.Builtin" "echo",
    ShellHighlight.shellTokenJson 4 "Token.Text" "\t",
    ShellHighlight.shellTokenJson 5 "Token.Literal.String.Double" "\"ready\"",
    ShellHighlight.shellTokenJson 12 "Token.Text" "\n\n",
    ShellHighlight.shellTokenJson 14 "Token.Name.Variable" "$HOME",
    ShellHighlight.shellTokenJson 19 "Token.Text" "  ",
    ShellHighlight.shellTokenJson 21 "Token.Comment.Single" "# terminal\t  \n"]]

def prepared (markdown : Bool) (input : String) : Elab.Prepared × Array Diag :=
  let (raws, ds) := if markdown then Md.read "listing.md" input else
    let (toks, ld) := Lex.lex "listing.tex" input
    let (raws, pd) := Parse.parse "listing.tex" toks
    (raws, ld ++ pd)
  (Elab.prepare "listing" raws, ds)

def invocationReply (kind : String) : String :=
  ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson
    (ListingReply.Request.ofSource "bash" "sample")
    #[ShellHighlight.shellTokenJson 0 kind "sample\n"]]

def invocationStub (replyName : String) : String :=
  "#!/bin/sh\n\
if [ \"$1\" != -I ] || [ \"$2\" != -B ] || [ \"$3\" != -c ]; then exit 2; fi\n\
reply=\"${0%/*}/" ++ replyName ++ "\"\n\
[ -r \"$reply\" ] || exit 3\n\
exec /bin/cat \"$reply\"\n"

-- The child owns PATH; the suite's environment and working directory stay put.
def invocationProbe (dir : System.FilePath) : IO (List String) := do
  let ref ← IO.mkRef ([] : List String)
  let request := ListingReply.Request.ofSource "bash" "sample"
  let expect (label : String) (kind : LeanTex.Core.ListingHighlight.Kind) : IO Unit := do
    let (answers, ds) ← LeanTex.Cli.ListingHighlight.fulfil "listing.tex" #[request]
    check ref label (ds.isEmpty && answers.size == 1 && answers.all fun answer =>
      answer.request == request && answer.tokens == #[#[{ kind, text := "sample" }]])
  let selected := dir / "selected environment"
  expect "selected symlink preserves its environment and source" .keyword
  IO.FS.writeFile (selected / "reply.json") (invocationReply "Token.Name.Builtin")
  expect "same request observes changed environment" .nameBuiltin
  IO.FS.removeFile (selected / "reply.json")
  let (answers, ds) ← LeanTex.Cli.ListingHighlight.fulfil "listing.tex" #[request]
  check ref "missing provider returns no answer and one keyed warning"
    (answers.isEmpty && ds.size == 1 &&
      ds.all fun d => d.code == "W0393" && d.subject == some "listing-language:bash")
  IO.FS.writeFile (selected / "reply.json") (invocationReply "Token.Name.Builtin")
  expect "restored provider retries the unchanged request" .nameBuiltin
  IO.FS.writeFile (dir / "base-python") (invocationStub "replacement.json")
  expect "same invocation observes a replaced interpreter" .number
  return (← ref.get).reverse

end Tests.ListingProvider

namespace Tests

/-- Invocation spelling selects the provider environment even when several
paths resolve to one executable. Fresh fulfilments must observe environment
and interpreter changes, including recovery after an unavailable provider. -/
def listingProviderInvocationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some lean ← ToolProbe.onPath "lean" |
    throw <| IO.userError "listing invocation checks require the Lean interpreter"
  let lean := (← IO.currentDir) / lean
  for mode in ["absolute", "relative", "empty"] do
    IO.FS.withTempDir fun dir => do
      let selected := dir / "selected environment"
      IO.FS.createDir selected
      IO.FS.writeFile (dir / "base-python") (ListingProvider.invocationStub "reply.json")
      discard <| IO.Process.run {
        cmd := "/bin/chmod",
        args := #["+x", (dir / "base-python").toString] }
      discard <| IO.Process.run {
        cmd := "/bin/ln",
        args := #["-s", (dir / "base-python").toString, (selected / "python3").toString] }
      IO.FS.writeFile (selected / "reply.json")
        (ListingProvider.invocationReply "Token.Keyword")
      IO.FS.writeFile (selected / "replacement.json")
        (ListingProvider.invocationReply "Token.Literal.Number")
      let driver := dir / "invocation.lean"
      IO.FS.writeFile driver <|
        "import Tests.ListingProvider\n\
def main (args : List String) : IO UInt32 := do\n\
  let [dir] := args | throw (IO.userError \"expected one fixture directory\")\n\
  let failures ← Tests.ListingProvider.invocationProbe dir\n\
  for failure in failures do IO.println failure\n\
  return if failures.isEmpty then 0 else 1\n"
      let path := if mode == "absolute" then selected.toString
        else if mode == "relative" then "selected environment" else ""
      let result ← RunBounded.output {
        cmd := lean.toString, args := #["--run", driver.toString, dir.toString],
        cwd := if mode == "empty" then selected else dir,
        env := #[("PATH", some path)] }
      check ref s!"listing provider/{mode}: {result.stdout}{result.stderr}"
        (result.exitCode == 0)

/-- Checked replies must reach real frontend listings and both artifacts.
Missing, stale, foreign and forged replies keep the source without class paint;
completed refusals retain their typed, keyed diagnostic on re-elaboration. -/
def listingProviderChecks (ref : IO.Ref (List String)) : IO Unit := do
  listingProviderInvocationChecks ref
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
        (terminalLf := true)
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
    for (word, kind) in [("echo", LeanTex.Core.ListingHighlight.Kind.nameBuiltin),
        ("ready", ⟨"Literal.String.Double"⟩), ("$HOME", ⟨"Name.Variable"⟩),
        ("# terminal", ⟨"Comment.Single"⟩)] do
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
    -- Exact source still belongs to the language that requested its classes.
    let foreign := answers.map fun a =>
      { a with request := { a.request with language := "foreign-language" } }
    for rejected in [#[], forged, stale, foreign] do
      let (plain, _, _) := Elab.runPrepared "listing" { base with listingReplies := rejected } earlier
      let (_, plainBody, _) := HtmlDoc.emitTree {} plain
      let (_, coldBody, _) := HtmlDoc.emitTree {} cold
      t "listing provider: missing, stale, foreign and forged answers ship the original plain page"
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
