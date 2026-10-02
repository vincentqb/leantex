import Tests.ListingHighlight

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

end Tests.ShellHighlight

namespace Tests

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
    let aliases := if probe.name == "basic" then ["bash", "sh", "shell"] else ["bash"]
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
