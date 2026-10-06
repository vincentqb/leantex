import Tests.ListingHighlight
import LeanTex.Core.ListingReply

open LeanTex.Core

namespace Tests.ShellHighlight

open LeanTex.Core.ListingHighlight (Kind)

inductive Paint where
  | ink (kind : Kind)
  | variable
  deriving Inhabited

structure Probe where
  name : String
  source : String
  pins : Array (String × Paint) := #[]

/- Shell syntax references: POSIX.1-2024, Shell Command Language §2.2–2.3,
https://pubs.opengroup.org/onlinepubs/9799919799/utilities/V3_chap02.html
and Bash 5.3 manual §3.1.2, §3.5.3–3.5.4, §3.6.6,
https://www.gnu.org/software/bash/manual/bash.html.
The simple colour pins use the existing Default/Friendly shared classes.
Variables must differ from literal strings without fixing a Pygments subtype
to the coarse `name` colour. Complex constructs owe conservation here. -/
def shellProbes : Array Probe := #[
  -- EOF and LF must give comments the same class ink in both artifacts.
  -- The trailing spaces and tab remain authored source, even at EOF.
  { name := "final-inline",
    source := "echo first  # earlier\n\n\tprintf last\t  # terminal  ",
    pins := #[("# earlier", .ink .comment), ("# terminal", .ink .comment)] },
  { name := "final-standalone",
    source := "# heading\nprintf next\n# ending",
    pins := #[("# heading", .ink .comment), ("# ending", .ink .comment)] },
  { name := "final-hash-context",
    source := "echo '# quoted' word#hash \\#literal  # trailing",
    pins := #[("# quoted", .ink .string), ("word#hash", .ink .plain),
      ("literal", .ink .plain), ("# trailing", .ink .comment)] },
  { name := "basic",
    source := "if test -n \"$VALUE\"; then\n\techo '<ready>&' && printf 42\nfi\n# boundary comment\npwd",
    pins := #[("if", .ink .keyword), ("then", .ink .keyword),
      ("fi", .ink .keyword), ("echo", .ink .builtin),
      ("<ready>&", .ink .string), ("42", .ink .number),
      ("&&", .ink .operator), ("# boundary comment", .ink .comment),
      ("$VALUE", .variable)] },
  { name := "quoting",
    source := "echo '$SINGLE' \"$DOUBLE \\$QUOTED\" \\$ESCAPED x#y\n# real comment\nprintf done",
    pins := #[("$SINGLE", .ink .string), ("$DOUBLE", .variable),
      ("QUOTED", .ink .string), ("ESCAPED", .ink .plain),
      ("x#y", .ink .plain), ("# real comment", .ink .comment)] },
  { name := "parameters",
    source := "printf '%s' \"$1\" \"$?\" \"${HOME:-fallback}\"",
    pins := #[("$1", .variable), ("$?", .variable), ("HOME", .variable)] },
  { name := "substitutions",
    source := "echo \"$(printf '%s' \"$HOME\")\"\necho `printf next` | cat > output\n" },
  { name := "here-document",
    source := "cat <<'END'\n$HOME # literal <body>&\nEND\ncat <<-STOP\n\t${HOME}\n\tSTOP\necho done" },
  { name := "multiline",
    source := "echo \"first\n\tsecond $HOME\"\n\nprintf 'héllo\n  λ'\necho x\\\n  y" },
  { name := "unfinished-double", source := "echo \"open\t${HOME:-value\n  tail" },
  { name := "unfinished-single", source := "echo 'open\\quote\n\t$HOME # tail" },
  { name := "unfinished-escape", source := "echo tail\\" },
  { name := "line-endings", source := "echo first\r\n\t# comment\r\n\r\nprintf '<last>&'\r\n" }]

def visible (c : Char) : Bool := !c.isWhitespace && c != '\u00a0'

def visibleText (s : String) : Array Char := s.toList.toArray.filter visible

/-- A unique source occurrence fixes the glyph positions being judged:
another occurrence elsewhere with the right colour cannot satisfy a pin. -/
def witnessIndex? (source needle : String) : Option Nat := Id.run do
  let text := visibleText source
  let word := visibleText needle
  if word.isEmpty || word.size > text.size then return none
  let mut found := none
  for i in [0:text.size - word.size + 1] do
    if text.extract i (i + word.size) == word then
      if found.isSome then return none
      found := some i
  return found

def witnessPaint? (source needle : String) (glyphs : Array (Char × α)) :
    Option (Array α) := do
  let start ← witnessIndex? source needle
  let word := visibleText needle
  let kept := glyphs.filter fun (c, _) => visible c
  let run := kept.extract start (start + word.size)
  if run.map (·.1) == word then some (run.map (·.2)) else none

mutual

/-- Read inherited token paint from the typed code subtree, including nested
strong/em elements and text split across several spans. -/
def htmlPaintOne (color : Option String) (acc : Array (Char × Option String)) :
    Html.Node → Array (Char × Option String)
  | .text text => acc ++ text.toList.toArray.map (·, color)
  | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    let own := (attrs.find? fun (key, value) =>
      tag == "span" && key == "style" && hasStr value "color:").map (·.2)
    htmlPaintList (own.or color) acc kids.toList

def htmlPaintList (color : Option String) (acc : Array (Char × Option String)) :
    List Html.Node → Array (Char × Option String)
  | [] => acc
  | node :: rest => htmlPaintList color (htmlPaintOne color acc node) rest

end

def minted (language : String) (style : Ir.ListingStyle) (source : String) :
    Ir.Doc × Array Diag :=
  let styleName := if style == .friendly then "friendly" else "default"
  elabStr (dvDoc "\\usepackage{minted}\n"
    ("\\begin{minted}[style=" ++ styleName ++ "]{" ++ language ++ "}\n" ++
      source ++ "\n\\end{minted}"))

def shellTokenJson (offset : Nat) (kind text : String) : Lean.Json :=
  Lean.Json.mkObj [("offset", Lean.toJson offset),
    ("kind", Lean.toJson kind), ("text", Lean.toJson text)]

def shellSuccessJson (request : ListingReply.Request)
    (tokens : Array Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("language", Lean.toJson request.language),
    ("source", Lean.toJson request.source), ("tokens", .arr tokens)]

def shellFailureJson (request : ListingReply.Request) (error : String) : Lean.Json :=
  Lean.Json.mkObj [("language", Lean.toJson request.language),
    ("source", Lean.toJson request.source), ("error", Lean.toJson error)]

def shellBatchJson (answers : Array Lean.Json)
    (provider : String := "Pygments") (version : Nat := 1) : String :=
  (Lean.Json.mkObj [("version", Lean.toJson version),
    ("provider", Lean.toJson provider),
    ("providerVersion", Lean.toJson "fixture"), ("answers", .arr answers)]).compress

def shellDecodeRejected (requests : Array ListingReply.Request) (body : String) : Bool :=
  match ListingReply.decode requests body with
  | .error _ => true
  | .ok _ => false

end Tests.ShellHighlight

namespace Tests

/-- The external boundary is tested as data: arbitrary class names cannot
inject markup or paint, and neither token offsets nor text may change source.
No installed Python module or document code runs in this check. -/
def shellReplyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let project := ListingReply.projectKind
  for (name, kind) in [
      ("Token.Keyword.Reserved", .keyword), ("Token.Comment.Hashbang", .comment),
      ("Token.Literal.String.Double", .string), ("Token.Literal.Number.Hex", .number),
      ("Token.Name.Builtin.Pseudo", .builtin), ("Token.Name.Variable.Global", .name),
      ("Token.Operator.Word", .operator), ("Token.Name.Builtinish", .name),
      ("Token.Punctuation", .plain), ("Token.Error", .plain),
      ("Token.Text.Whitespace", .plain), ("Token.Generic.Deleted", .plain),
      ("Token.Names.Builtin", .plain), ("Token.Keywordish", .plain),
      ("Other.Keyword", .plain), ("color:red", .plain), ("<script>", .plain),
      ("", .plain)] do
    t s!"listing reply: whole token ancestry {name}" (project name == kind)
  let normalized := ListingReply.Request.ofSource " BaSh " "\r\n\n\techo λ\r\n  \r\n"
  t "listing reply: normalize once, retaining the second leading blank"
    (normalized == { language := "bash", source := "\n\techo λ" } &&
      normalized.lines == #["", "\techo λ"])
  let request : ListingReply.Request :=
    { language := "bash", source := "echo\t\"λ😀\"\n\n$HOME" }
  let records := #[
    ShellHighlight.shellTokenJson 0 "Token.Name.Builtin" "echo",
    ShellHighlight.shellTokenJson 4 "Token.Text" "\t",
    ShellHighlight.shellTokenJson 5 "Token.Literal.String.Double" "\"λ😀\"",
    ShellHighlight.shellTokenJson 9 "Token.Text" "\n\n",
    ShellHighlight.shellTokenJson 11 "Token.Name.Variable" "$HOME"]
  let answer := ShellHighlight.shellSuccessJson request records
  let body := ShellHighlight.shellBatchJson #[answer]
  let .ok (answers, ds) := ListingReply.decode #[request] body
    | failures ref "listing reply: valid Unicode, tab and blank-line reply rejected"
  t "listing reply: Unicode character offsets, source and classes agree"
    (ds.isEmpty && answers.size == 1 && answers.all fun a =>
      a.request == request && a.tokens.map LeanTex.Core.ListingHighlight.lineText ==
        #["echo\t\"λ😀\"", "", "$HOME"] &&
      a.tokens.flatten.map (·.kind) == #[.builtin, .plain, .string, .name])
  t "listing reply: lookup validates the original raw source"
    ((ListingReply.lookup answers " BASH " ("\n" ++ request.source ++ "\n")).isSome &&
      (ListingReply.lookup answers "sh" request.source).isNone &&
      (ListingReply.lookup answers "bash" (request.source ++ " changed")).isNone)
  let forged : ListingReply.Answer :=
    { request, tokens := #[#[{ kind := .keyword, text := "changed" }]] }
  t "listing reply: matching cache key cannot authorize changed token text"
    ((ListingReply.lookup #[forged] "bash" request.source).isNone)
  let rawLines : Array String := #[
    "", " ", "\n\n\techo x\r\n\r\n", "echo \"unfinished\t${HOME",
    "echo 'open\n\t$HOME # literal", "echo tail\\", "cat <<'END'\n$HOME\nEND",
    "echo \"$(printf '%s' \"$HOME\")\"", "x#y\n# comment", "<tag>&\"λ😀\""]
  for raw in rawLines do
    let r := ListingReply.Request.ofSource "bash" raw
    let pieces := if r.source.isEmpty then #[] else
      #[ShellHighlight.shellTokenJson 0 "Token.Unknown.Future" r.source]
    let .ok (as, _) := ListingReply.decode #[r]
        (ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson r pieces])
      | failures ref "listing reply: source-conserving plain classification rejected"
    t "listing reply: empty, unclosed and multiline content survives exactly"
      (as.all fun a => a.tokens.map LeanTex.Core.ListingHighlight.lineText == r.lines)
    t "listing reply: unknown token classes leave plain paint"
      (as.all fun a => a.tokens.flatten.all (·.kind == .plain))
  -- The lexer boundary may be part of the final token or a separate token.
  -- Deliberately bypass normalization here to include authored trailing LFs.
  for source in ["", "\n", "\n\n", "\n\techo λ😀  ", "echo x\n\n", "# tail\t  "] do
    let r : ListingReply.Request := { language := "bash", source }
    let boundary := ShellHighlight.shellTokenJson source.length "Token.Text" "\n"
    for pieces in [
        #[ShellHighlight.shellTokenJson 0 "Token.Comment.Single" (source ++ "\n")],
        #[ShellHighlight.shellTokenJson 0 "Token.Comment.Single" source, boundary]] do
      let body := ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson r pieces]
      let .ok (as, errors) := ListingReply.decode #[r] body (terminalLf := true)
        | failures ref "listing reply: exact terminal LF rejected"
      t "listing reply: terminal LF keeps the content key and all authored whitespace"
        (errors.isEmpty && as.size == 1 && as.all fun a =>
          a.request == r && a.tokens.map LeanTex.Core.ListingHighlight.lineText == r.lines)
      t "listing reply: raw mode still rejects the lexer-only LF"
        (ShellHighlight.shellDecodeRejected #[r] body)
    for text in [source, source ++ "\n\n", source ++ " \n", source ++ "\r\n"] do
      t "listing reply: terminal LF must be exactly one LF beyond the source"
        (match ListingReply.decode #[r] (ShellHighlight.shellBatchJson #[
            ShellHighlight.shellSuccessJson r #[
              ShellHighlight.shellTokenJson 0 "Token.Text" text]]) (terminalLf := true) with
          | .error _ => true
          | .ok _ => false)
    let badOffset := ShellHighlight.shellTokenJson (source.length + 1) "Token.Text" "\n"
    t "listing reply: terminal LF does not waive contiguous Unicode offsets"
      (match ListingReply.decode #[r] (ShellHighlight.shellBatchJson #[
          ShellHighlight.shellSuccessJson r #[
            ShellHighlight.shellTokenJson 0 "Token.Text" source, badOffset]])
          (terminalLf := true) with
        | .error _ => true
        | .ok _ => false)
  let encoded := ListingReply.encode #[normalized, request, { language := "", source := "" }]
  let .ok json := Lean.Json.parse encoded | failures ref "listing reply: encoding invalid JSON"
  let .ok encodedRequests := json.getObjValAs? (Array Lean.Json) "requests"
    | failures ref "listing reply: encoding missing requests"
  t "listing reply: request JSON round-trips every field, including empty values"
    (json.getObjValAs? Nat "version" == .ok 1 &&
      encodedRequests.map (fun j =>
        (j.getObjValAs? String "language", j.getObjValAs? String "source")) ==
      #[(.ok normalized.language, .ok normalized.source),
        (.ok request.language, .ok request.source), (.ok "", .ok "")])
  t "listing reply: empty batch is a valid complete response"
    (match ListingReply.decode #[] (ShellHighlight.shellBatchJson #[]) with
      | .ok (as, errors) => as.isEmpty && errors.isEmpty
      | .error _ => false)
  let brokenRecords := [
    records.set! 1 (ShellHighlight.shellTokenJson 99 "Token.Text" "\t"),
    records.set! 1 (ShellHighlight.shellTokenJson 4 "Token.Text" "    "),
    records.set! 2 (ShellHighlight.shellTokenJson 5 "Token.Literal.String" "\"λ\""),
    records.set! 3 (ShellHighlight.shellTokenJson 13 "Token.Text" "\n\n"),
    records.push (ShellHighlight.shellTokenJson 16 "Token.Text" "\n"),
    records.extract 1 records.size,
    records.reverse]
  for bad in brokenRecords do
    t "listing reply: gaps, byte offsets, expanded tabs, lost and inserted text rejected"
      (ShellHighlight.shellDecodeRejected #[request]
        (ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson request bad]))
  let malformed := [
    "{}",
    ShellHighlight.shellBatchJson #[answer] (version := 2),
    ShellHighlight.shellBatchJson #[answer] (provider := "Other"),
    ShellHighlight.shellBatchJson #[],
    ShellHighlight.shellBatchJson #[answer, answer],
    ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson normalized records],
    ShellHighlight.shellBatchJson #[Lean.Json.mkObj [
      ("language", Lean.toJson request.language), ("source", Lean.toJson request.source),
      ("tokens", .arr records), ("error", Lean.toJson "failed")]],
    ShellHighlight.shellBatchJson #[ShellHighlight.shellFailureJson request ""],
    ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson request
      #[Lean.Json.mkObj [("offset", Lean.toJson (-1 : Int)),
        ("kind", Lean.toJson "Token.Text"), ("text", Lean.toJson request.source)]]]]
  for bad in malformed do
    t "listing reply: malformed or foreign batch is rejected atomically"
      (ShellHighlight.shellDecodeRejected #[request] bad)
  let other : ListingReply.Request := { language := "ruby", source := "puts 7" }
  let otherAnswer := ShellHighlight.shellSuccessJson other
    #[ShellHighlight.shellTokenJson 0 "Token.Text" other.source]
  t "listing reply: reordered content keys are rejected"
    (ShellHighlight.shellDecodeRejected #[request, other]
      (ShellHighlight.shellBatchJson #[otherAnswer, answer]))
  t "listing reply: a valid prefix cannot hide a malformed later answer"
    (ShellHighlight.shellDecodeRejected #[other, request]
      (ShellHighlight.shellBatchJson #[otherAnswer,
        ShellHighlight.shellSuccessJson request (records.extract 1 records.size)]))
  for error in ["unsupported", "unavailable", "failed", "<unsafe>\nprivate details"] do
    let refusal := ShellHighlight.shellBatchJson #[ShellHighlight.shellFailureJson request error]
    let .ok (plain, failures) := ListingReply.decode #[request] refusal
      | failures ref "listing reply: completed per-request refusal was not recorded"
    let expected : ListingReply.Failure := match error with
      | "unsupported" => .unsupported
      | "unavailable" => .unavailable
      | _ => .rejected
    t "listing reply: refusal carries exact plain source and a keyed typed failure"
      (plain == #[ListingReply.plainAnswer request] &&
        failures == #[(request, expected)] &&
        failures.all fun (_, failure) =>
          !hasStr failure.reason "<unsafe>" && !hasStr failure.reason "private details")
    t "listing reply: repeated refusal replays the identical typed failure"
      (match ListingReply.decode #[request] refusal with
        | .ok (_, replay) => replay == failures
        | .error _ => false)
    t "listing reply: terminal LF mode leaves keyed refusals unchanged"
      (match ListingReply.decode #[request] refusal (terminalLf := true) with
        | .ok (replayedPlain, replay) => replayedPlain == plain && replay == failures
        | .error _ => false)
  let native := ListingHighlight.sourceDoc "python" "print(7)"
  let lean := ListingHighlight.sourceDoc "lean4" "def n := 7"
  let bash := (ShellHighlight.minted "bash" .default "echo x").1
  let friendly := (ShellHighlight.minted "bash" .friendly "echo x").1
  let markdown := (elabMd "```bash\necho x\n```").1
  let ruby := ListingHighlight.sourceDoc "ruby" "puts 7"
  let combined := { bash with
    body := native.body ++ lean.body ++
      #[.center (bash.body ++ #[.quote (friendly.body ++ markdown.body)] ++ ruby.body)] }
  let collected := ListingReply.requests combined
  t "listing reply: generic fold finds nested requests, dedupes surfaces and styles"
    (collected == #[{ language := "bash", source := "echo x" },
      { language := "ruby", source := "puts 7" }])
  t "listing reply: native Lean and Python need no external request"
    ((ListingReply.requests native).isEmpty && (ListingReply.requests lean).isEmpty)

/-- Fail-before artifact guard, independent of native versus external lexing.
The optional fulfiller is the CLI's effects-as-data seam; the default reads
the elaborator's own result. Tests never execute a shell, lexer or plugin.
Parent integration supplies the chosen fulfiller and registers this check. -/
def shellHighlightChecks (ref : IO.Ref (List String))
    (fulfil : Ir.Doc → IO Ir.Doc := pure) : IO Unit := do
  let t := check ref
  let some bytes ← findFont | failures ref "shell highlight: fixture font missing"
  let .ok font := Font.parse bytes | failures ref "shell highlight: fixture font invalid"
  let fonts := oneFaceOf font
  for probe in ShellHighlight.shellProbes do
    let aliases := if probe.name == "basic" || probe.name.startsWith "final-" then
      ["bash", "sh", "shell"] else ["bash"]
    for language in aliases do
      let inputs := [
        ("minted/default", Ir.ListingStyle.default,
          ShellHighlight.minted language .default probe.source),
        ("minted/friendly", Ir.ListingStyle.friendly,
          ShellHighlight.minted language .friendly probe.source),
        ("markdown/default", Ir.ListingStyle.default,
          elabMd ("```" ++ language ++ "\n" ++ probe.source ++ "\n```"))]
      for (surface, style, (rawDoc, ds)) in inputs do
        let label := s!"shell {surface}/{language}/{probe.name}"
        t s!"{label}: the real surface elaborates without error" (ds.all (·.severity != .error))
        let doc ← fulfil rawDoc
        let entries := ListingHighlight.listings doc
        let expectedLines := Ir.verbatimLines ("\n" ++ probe.source ++ "\n")
        let source := String.intercalate "\n" expectedLines.toList
        t s!"{label}: fulfillment preserves source, language and selected style"
          (entries.size == 1 && entries.all fun (_, text, spec) =>
            Ir.verbatimLines text == expectedLines &&
            spec.langToken == some language && spec.style == style &&
            (spec.tokenLines text).map LeanTex.Core.ListingHighlight.lineText == expectedLines)
        let (_, body, _) := HtmlDoc.emitTree {} doc
        let codes := ListingHighlight.codeNodesList #[] body.toList
        t s!"{label}: typed HTML preserves every source character"
          (codes.size == 1 && codes.all fun code => nodeTextOne "" code == source)
        let html := ShellHighlight.htmlPaintList none #[] codes.toList
        let out := layoutOf fonts doc
        let glyphs := ListingHighlight.glyphColors out
        t s!"{label}: Layout.Out preserves source glyph order"
          ((glyphs.filter fun (c, _) => ShellHighlight.visible c).map (·.1) ==
            ShellHighlight.visibleText source)
        let pdf := pdfText (Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info)
        let fg := (Ir.Design.ofDoc doc).fg
        let literal := (Listing.ink doc.palette none .string (style := style)).getD fg
        for (needle, paint) in probe.pins do
          t s!"{label}/{needle}: the source pin is unique"
            (ShellHighlight.witnessIndex? source needle).isSome
          let laid := ShellHighlight.witnessPaint? source needle glyphs
          let typed := ShellHighlight.witnessPaint? source needle html
          match paint with
          | .ink kind =>
            let ink := (Listing.ink doc.palette none kind (style := style)).getD fg
            t s!"{label}/{needle}: Layout.Out ships its class ink"
              (laid.any fun colors => !colors.isEmpty && colors.all (· == ink))
            -- Black may be the PDF graphics state's initial ink: an
            -- unpainted plain run owes no redundant colour operator.
            if kind != .plain then
              t s!"{label}/{needle}: emitted PDF contains its class paint"
                (bytesContain pdf ink.pdfFill)
            t s!"{label}/{needle}: typed HTML ships its class ink"
              (typed.any fun colors => !colors.isEmpty && colors.all fun color =>
                if kind == .plain then color.isNone
                else color.any fun css => hasStr css (HtmlDoc.cssColor ink))
          | .variable =>
            let ink := laid.bind (·[0]?)
            t s!"{label}/{needle}: variables have ink distinct from literal strings"
              (ink.any fun color => color != fg && color != literal &&
                laid.any fun colors => colors.all (· == color))
            t s!"{label}/{needle}: emitted PDF contains the variable paint"
              (ink.any fun color => color != fg && bytesContain pdf color.pdfFill)
            t s!"{label}/{needle}: typed HTML agrees with the variable glyph ink"
              (ink.any fun color => color != fg && typed.any fun colors =>
                !colors.isEmpty && colors.all fun css =>
                  css.any fun value => hasStr value (HtmlDoc.cssColor color))

end Tests
