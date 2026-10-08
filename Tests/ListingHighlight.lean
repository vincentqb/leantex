import Tests.Support

open LeanTex.Core

namespace Tests

namespace ListingHighlight

open LeanTex.Core.ListingHighlight (Language Kind Token tokenize lineText)

/-- Invented probes: keywords, literals and comments must ship distinct ink,
while indentation, empty lines and HTML metacharacters stay literal. -/
def pythonSource : String :=
  "def greet(value):\n    # Keep <tags> & quotes literal\n    return \"hello\" + str(42)\n\nprint(greet(7))"

def leanSource : String :=
  "def twice (n : Nat) : Nat :=\n  -- An invented example\n  n + 2\n#check \"<safe>&\""

def sourceDoc (language source : String) : Ir.Doc :=
  (elabStr (dvDoc "" ("\\begin{minted}{" ++ language ++ "}\n" ++ source ++
    "\n\\end{minted}"))).1

/-- Only listing leaves; the generic IR fold owns all container traversal. -/
def listings (doc : Ir.Doc) : Array (Option Ir.Color × String × Ir.ListingSpec) :=
  Ir.foldBlocks (fun acc b => match b with
      | .verbatim covered source spec => acc.push (covered, source, spec)
      | _ => acc) (fun acc _ => acc) #[] doc.body

def classified (language : Language) (source : String) : Array Token :=
  (tokenize language (Ir.verbatimLines source)).flatten

def hasToken (ts : Array Token) (kind : Kind) (text : String) : Bool :=
  ts.any fun t => t.kind == kind && t.text == text

mutual

/-- The actual code elements of a typed artifact, without its furniture. -/
def codeNodesOne (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .text _ | .style _ | .script _ _ => acc
  | n@(.elem tag _ kids) =>
    if tag == "code" then acc.push n else codeNodesList acc kids.toList

def codeNodesList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: ns => codeNodesList (codeNodesOne acc n) ns

end

mutual

/-- Only spans with explicit token paint count; a language class alone did
not colour the old artifact. -/
def coloredSpansOne (acc : Array (String × String)) : Html.Node →
    Array (String × String)
  | .text _ | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    let style := ((attrs.find? fun p => p.1 == "style").map (·.2)).getD ""
    let acc := if tag == "span" && hasStr style "color:" then
      acc.push (nodeTextList "" kids.toList, style) else acc
    coloredSpansList acc kids.toList

def coloredSpansList (acc : Array (String × String)) : List Html.Node →
    Array (String × String)
  | [] => acc
  | n :: ns => coloredSpansList (coloredSpansOne acc n) ns

end

def glyphColors (out : Layout.Out) : Array (Char × Ir.Color) := Id.run do
  let mut ink := #[]
  for page in out.pages do
    for line in page.lines do
      unless line.furniture do
        for seg in line.segs do
          if let .run _ color _ _ glyphs _ _ _ _ _ _ := seg then
            for (_, c, _) in glyphs do
              ink := ink.push (c, color)
  return ink

/-- Invented palette-epoch fixture, independent of option parsing. A frame's
entry pair applies until a body declaration replaces the default ink/ground. -/
def epochDoc (pal : Ir.Palette) (epoch : Option Ir.Palette)
    (standout : Bool) (valign : Ir.VAlign) : Ir.Doc :=
  let source := "return value"
  let code : Ir.Block := .verbatim none source
    { highlight := tokenize .python (Ir.verbatimLines source) }
  let body := (epoch.toArray.map Ir.Block.setPalette).push code
  { (elabStr (dvDeck "" "")).1 with
    palette := pal, body := #[.frame #[] standout valign false body] }

/-- A paint-level artifact probe: select the typed listing style and pass its
shared inlines through the real PDF/HTML emitters. Listing option parsing and
backend parameter threading are separate integration responsibilities. -/
def styleSource : String := "def demo(): return \"sample\" + str(42) # comment"

def styleDoc (style : Ir.ListingStyle) : Ir.Doc :=
  let doc := sourceDoc "python" styleSource
  let spec : Ir.ListingSpec :=
    { style, highlight := tokenize .python (Ir.verbatimLines styleSource) }
  let content := spec.tokenLines styleSource |>.flatten |>.map fun token =>
    Listing.tokenInline doc.palette none none token (style := spec.style)
  { doc with body := #[.para #[.styled .mono content]] }

mutual

def fontSpansOne (acc : Array (String × String)) : Html.Node → Array (String × String)
  | .text _ | .style _ | .script _ _ => acc
  | .elem tag _ kids =>
    let acc := if tag == "strong" || tag == "em" then
      acc.push (tag, nodeTextList "" kids.toList) else acc
    fontSpansList acc kids.toList

def fontSpansList (acc : Array (String × String)) : List Html.Node →
    Array (String × String)
  | [] => acc
  | node :: rest => fontSpansList (fontSpansOne acc node) rest

end

end ListingHighlight

/-- Selecting Friendly must change actual ink while conserving the code.
The colour pins are Pygments' `styles/friendly.py` (the whole table is held
to Pygments by `listingStyleTableChecks`); keywords stay bold and comments
italic in both styles. -/
def listingFriendlyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "listing style: bounded typed names leave unsupported styles unresolved"
    (Ir.ListingStyle.ofName? "default" == some .default &&
     Ir.ListingStyle.ofName? "friendly" == some .friendly &&
     Ir.ListingStyle.ofName? " friendly " == some .friendly &&
     (["", "Friendly", "friendly-extra", "unknown-style"] : List String).all
       fun name => (Ir.ListingStyle.ofName? name).isNone)
  let friendly := Ir.listingRoles.map fun (_, kind) =>
    (Listing.paint (Ir.Design.ofPalette {}) .friendly kind).map (·.color)
  t "listing friendly: the role types resolve to the style's sourced colours"
    (friendly == ([{ r := 0, g := 112, b := 32 }, { r := 64, g := 112, b := 160 },
      { r := 64, g := 160, b := 112 }, { r := 96, g := 160, b := 176 },
      { r := 0, g := 112, b := 32 }, { r := 6, g := 40, b := 126 },
      { r := 102, g := 102, b := 102 }] : List Ir.Color).map some)
  let authored := ({} : Ir.Palette).declare "codekeyword" Ir.Color.black
  t "listing friendly: authored roles take precedence over style defaults"
    (Listing.ink authored none .keyword (style := .friendly) == some Ir.Color.black)
  for theme in Theme.builtin do
    let d := Ir.Design.ofPalette theme.palette
    let grounds := [none, some d.standout.bg] ++
      (d.titlepage.toList.map fun pair => some pair.bg)
    for style in [Ir.ListingStyle.default, .friendly] do
      t s!"listing style: {repr style} text AA on every {theme.name} ground"
        (grounds.all fun ground => Listing.contract theme.palette ground (style := style))
  let some bytes ← findFont | failures ref "listing friendly: fixture font missing"
  let .ok font := Font.parse bytes | failures ref "listing friendly: fixture font invalid"
  let fonts := oneFaceOf font
  let defaultDoc := ListingHighlight.styleDoc .default
  let friendlyDoc := ListingHighlight.styleDoc .friendly
  let defaultOut := layoutOf fonts defaultDoc
  let friendlyOut := layoutOf fonts friendlyDoc
  let defaultPdf := pdfText (Pdf.write (Layout.Geom.ofPage defaultDoc.page) fonts
    defaultOut.pages defaultDoc.info)
  let friendlyPdf := pdfText (Pdf.write (Layout.Geom.ofPage friendlyDoc.page) fonts
    friendlyOut.pages friendlyDoc.info)
  let (_, defaultHtml, _) := HtmlDoc.emitTree {} defaultDoc
  let (_, friendlyHtml, _) := HtmlDoc.emitTree {} friendlyDoc
  let defaultSpans := ListingHighlight.coloredSpansList #[] defaultHtml.toList
  let friendlySpans := ListingHighlight.coloredSpansList #[] friendlyHtml.toList
  let keyword : Ir.Color := { r := 0, g := 112, b := 32 }
  t "listing friendly: changing only style changes shipped PDF glyph ink"
    ((ListingHighlight.glyphColors friendlyOut).any (fun (c, ink) =>
       c == 'd' && ink == keyword) &&
     !(ListingHighlight.glyphColors defaultOut).any (fun (_, ink) => ink == keyword))
  t "listing friendly: changing only style changes emitted PDF fill"
    (bytesContain friendlyPdf keyword.pdfFill && !bytesContain defaultPdf keyword.pdfFill)
  t "listing friendly: changing only style changes typed HTML ink"
    (friendlySpans.any (fun (text, style) =>
       text == "def" && hasStr style (HtmlDoc.cssColor keyword)) &&
     !defaultSpans.any (fun (_, style) => hasStr style (HtmlDoc.cssColor keyword)))
  for (style, html) in [(Ir.ListingStyle.default, defaultHtml), (.friendly, friendlyHtml)] do
    let spans := ListingHighlight.fontSpansList #[] html.toList
    t s!"listing style: {repr style} preserves source text and font distinctions"
      (nodeTextList "" html.toList == ListingHighlight.styleSource &&
       spans.contains ("strong", "def") && spans.contains ("em", "# comment"))
  let (_, diagnostics) := elabStr (dvDoc ""
    "\\begin{minted}[style=unknown-style]{python}\nprint(1)\n\\end{minted}")
  t "listing style: unsupported style still has its option warning"
    (diagnostics.any (·.code == "W0110"))
  -- The command path must select those inks too: a style in a spec built
  -- by the test alone cannot witness minted's source declaration.
  let code (opts : String := "") :=
    "\\begin{minted}" ++ (if opts.isEmpty then "" else "[" ++ opts ++ "]") ++
      "{python}\ndef f(): return 7\n\\end{minted}\n"
  let defaultKeyword : Ir.Color := { r := 0, g := 128, b := 0 }
  for (name, pre, body, wanted) in [
      ("global", "\\setminted{style=friendly}", code "", #[keyword]),
      ("lexer", "\\setminted{style=friendly}\\setminted[python]{style=default}",
        code "", #[defaultKeyword]),
      ("local", "\\setminted[python]{style=default}", code "style=friendly", #[keyword]),
      ("scope", "\\setminted{style=default}",
        "{\\setminted{style=friendly}" ++ code "" ++ "}\n" ++ code "",
        #[keyword, defaultKeyword])] do
    let (doc, ds) := elabStr (dvDoc pre body)
    let out := layoutOf fonts doc
    let (_, html, _) := HtmlDoc.emitTree {} doc
    let spans := ListingHighlight.coloredSpansList #[] html.toList
    let keywordSpans := spans.filter (·.1 == "def")
    let actual := (ListingHighlight.glyphColors out).filterMap fun (c, ink) =>
      if c == 'd' then some ink else none
    t s!"listing style source: {name} selects shipped PDF ink"
      (actual == wanted)
    t s!"listing style source: {name} selects typed HTML ink"
      (keywordSpans.size == wanted.size &&
        (keywordSpans.zip wanted).all fun ((_, css), color) =>
          hasStr css (HtmlDoc.cssColor color))
    t s!"listing style source: {name} is accounted without an option refusal"
      (!(ds.any fun d => d.code == "W0110" || d.code == "W0301"))
  t "listing style source: a listings named style is still diagnosed"
    ((warnCodes (dvDoc "" "\\begin{lstlisting}[style=friendly]\nx\n\\end{lstlisting}")).contains
      "W0110")

/-- Classification boundaries and losslessness are independent checks: a
lexer that preserves text but classifies every scalar plain fails the first;
a lexer that finds the right keywords but drops whitespace fails the second. -/
def listingLexerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let lean := ListingHighlight.classified .lean
    "def count' (α : Type) :=\n/- outer\n /- nested -/ still outer -/\n\"a\\\"b\" ++ 'x'\n#check 0x2a"
  t "highlight lexer: Lean declarations, Unicode names and apostrophes"
    (ListingHighlight.hasToken lean .keyword "def" &&
     ListingHighlight.hasToken lean .nameFunction "count'" &&
     lean.any (fun token => token.kind == .text && token.text.contains 'α') &&
     ListingHighlight.hasToken lean .nameBuiltin "Type")
  t "highlight lexer: nested Lean comments retain multiline state"
    (ListingHighlight.hasToken lean .comment "/- outer" &&
     ListingHighlight.hasToken lean .comment " /- nested -/ still outer -/")
  t "highlight lexer: Lean escaped strings, characters, commands and hex"
    (ListingHighlight.hasToken lean .string "\"a\\\"b\"" &&
     ListingHighlight.hasToken lean .string "'x'" &&
     ListingHighlight.hasToken lean .keyword "#check" &&
     ListingHighlight.hasToken lean .number "0x2a")
  let python := ListingHighlight.classified .python
    "def sample(value):\n  r\"a\\\"b\" # comment\n  '''first\nsecond'''\n  return f\"{value}\" + str(1.25e-2)"
  t "highlight lexer: Python declarations, comments and prefixed strings"
    (ListingHighlight.hasToken python .keyword "def" &&
     ListingHighlight.hasToken python .nameFunction "sample" &&
     ListingHighlight.hasToken python .comment "# comment" &&
     ListingHighlight.hasToken python .string "r\"a\\\"b\"")
  t "highlight lexer: Python triples, f-string floor and numeric exponent"
    (ListingHighlight.hasToken python .string "'''first" &&
     ListingHighlight.hasToken python .string "second'''" &&
     ListingHighlight.hasToken python .string "f\"{value}\"" &&
     ListingHighlight.hasToken python .nameBuiltin "str" &&
     ListingHighlight.hasToken python .number "1.25e-2")
  for language in [LeanTex.Core.ListingHighlight.Language.lean, .python] do
    let alphabet := "ab_λ0'\"`#\\/-+<>& \t\n\r«»".toList.toArray
    let mut seed : UInt64 := 17
    for n in [:256] do
      let mut source := ""
      for _ in [:n] do
        let (i, next) := rand seed alphabet.size
        seed := next
        source := source.push alphabet[i]!
      let lines := ((source.splitOn "\n").map id).toArray
      t s!"highlight lexer: exact scalar/whitespace reconstruction {repr language} {n}"
        ((LeanTex.Core.ListingHighlight.tokenize language lines).map
          LeanTex.Core.ListingHighlight.lineText == lines)
  let source := "\n  literal <tag>\n\nnext\tline\n"
  let stale : Ir.ListingSpec :=
    { highlight := #[#[{ kind := .keyword, text := "wrong source" }]] }
  t "highlight IR: stale classification falls back to exact source"
    ((stale.tokenLines source).map LeanTex.Core.ListingHighlight.lineText ==
      Ir.verbatimLines source)

/-- Body epochs must paint the same listing ink and ground in both artifacts.
The unchanged entry is the control; a repeated declaration still resets a
title/standout pair, and a removed ground must not retain that entry's colour. -/
def listingPaletteEpochChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let light := ({} : Ir.Palette).declare "fg" Ir.Color.black
    |>.declare "bg" Ir.Color.white
    |>.declare "standoutfg" Ir.Color.white |>.declare "standoutbg" Ir.Color.black
    |>.declare "titlepagefg" Ir.Color.white |>.declare "titlepagebg" Ir.Color.black
  let dark := light.declare "fg" Ir.Color.white |>.declare "bg" Ir.Color.black
  let removed := { light with
    entries := light.entries.filter fun (role, _) => role != "fg" && role != "bg" }
  for (frame, standout, valign) in
      [("normal", false, Ir.VAlign.center), ("title", false, .golden),
       ("standout", true, .center)] do
    for (name, initial, epoch) in
        [("entry", light, none), ("dark", light, some dark),
         ("repeated", light, some light), ("removed", dark, some removed),
         ("light", dark, some light)] do
      let doc := ListingHighlight.epochDoc initial epoch standout valign
      let pal := epoch.getD initial
      let design := Ir.Design.ofPalette pal
      let ground := match epoch with
        | some p => p.find? "bg"
        | none => Ir.frameGroundOf initial standout valign
      let fg := if epoch.isSome then design.fg else if standout then design.standout.fg
        else if valign matches .golden then (design.titlepage.map (·.fg)).getD design.fg
        else design.fg
      let bg := ground.getD design.bg
      let keyword := (Listing.ink pal ground .keyword).getD fg
      let out := layoutOf fonts doc
      let glyphs := ListingHighlight.glyphColors out
      let geom := Layout.Geom.ofPage doc.page
      let shippedGround := out.pages[0]?.bind fun page =>
        page.fills[0]?.bind fun fill =>
          if fill.x == 0 && fill.y == 0 && fill.w == geom.pageW && fill.h == geom.pageH
          then some fill.color else none
      t s!"listing epoch {frame}/{name}: shipped PDF ink and page ground"
        (out.pages.size == 1 && shippedGround == ground &&
         glyphs.any (fun (c, color) => c == 'v' && color == fg) &&
         glyphs.any (fun (c, color) => c == 'r' && color == keyword) &&
         glyphs.all (fun (_, color) => Contrast.contrastMilli color bg ≥ Contrast.aaText))
      let pdf := pdfText (Pdf.write geom fonts out.pages doc.info)
      t s!"listing epoch {frame}/{name}: emitted PDF paints the classified ink"
        (bytesContain pdf fg.pdfFill && bytesContain pdf keyword.pdfFill)
      let (_, html, _) := HtmlDoc.emitTree {} doc
      let pre := elemAttrsList (· == "pre") #[] html.toList
      let code := ListingHighlight.codeNodesList #[] html.toList
      let spans := ListingHighlight.coloredSpansList #[] code.toList
      let paint := s!"background: {HtmlDoc.cssColor bg}; color: {HtmlDoc.cssColor fg}"
      t s!"listing epoch {frame}/{name}: typed HTML projects PDF ink and ground"
        (pre.size == 1 && pre.any (fun (_, attrs) =>
           attrs.any fun (key, value) => key == "style" && hasStr value paint) &&
         spans.any (fun (text, style) =>
           text == "return" && hasStr style (HtmlDoc.cssColor keyword)))
      t s!"listing epoch {frame}/{name}: typed HTML keeps the literal code"
        (code.size == 1 && nodeTextOne "" code[0]! == "return value")

/-- The last epoch is the persistent ground, even after a styled frame closes
or spills. Removing `bg` ships no fill; declaring it again resumes painting. -/
def listingPaletteContinuationChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let light := ({} : Ir.Palette).declare "fg" Ir.Color.black
    |>.declare "bg" Ir.Color.white
    |>.declare "standoutfg" Ir.Color.white |>.declare "standoutbg" Ir.Color.black
    |>.declare "titlepagefg" Ir.Color.white |>.declare "titlepagebg" Ir.Color.black
  let dark := light.declare "fg" Ir.Color.white |>.declare "bg" Ir.Color.black
  let removed := light.erase "bg"
  let code (source : String) : Ir.Block :=
    .verbatim none source
      { highlight := ListingHighlight.tokenize .python (Ir.verbatimLines source) }
  let pageGround (geom : Layout.Geom) (page : Layout.PageOut) : Option Ir.Color :=
    page.fills[0]?.bind fun fill =>
      if fill.x == -geom.bleed && fill.y == -geom.bleed &&
          fill.w == geom.pageW + 2 * geom.bleed &&
          fill.h == geom.pageH + 2 * geom.bleed then some fill.color else none
  for (name, standout, valign) in
      [("normal", false, Ir.VAlign.center), ("title", false, .golden),
       ("standout", true, .center)] do
    let frame (epoch : Option Ir.Palette) : Ir.Block :=
      .frame #[] false .center false
        ((epoch.toArray.map Ir.Block.setPalette).push (code "return value"))
    let doc := { (ListingHighlight.epochDoc light (some dark) standout valign) with
      body := #[.frame #[] standout valign false
          #[.setPalette dark, code "return value"],
        frame none, frame (some removed), frame none, frame (some light), frame none] }
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf fonts doc
    let expected := #[dark, dark, removed, removed, light, light]
    t s!"listing epoch {name}: a later frame keeps the current ground, including removal"
      (out.pages.size == expected.size &&
       (out.pages.zip expected).all fun (page, pal) =>
         let ground := pal.find? "bg"
         let design := Ir.Design.ofPalette pal
         let glyphs := ListingHighlight.glyphColors { pages := #[page], diags := #[] }
         pageGround geom page == ground &&
         glyphs.any (fun (c, color) => c == 'v' && color == design.fg) &&
         glyphs.all (fun (_, color) =>
           Contrast.contrastMilli color (ground.getD design.bg) ≥ Contrast.aaText))
    let (_, html, _) := HtmlDoc.emitTree {} doc
    let pre := elemAttrsList (· == "pre") #[] html.toList
    let codes := ListingHighlight.codeNodesList #[] html.toList
    t s!"listing epoch {name}: typed HTML keeps the outgoing palette across frames"
      (pre.size == expected.size && codes.size == expected.size &&
       ((pre.zip codes).zip expected).all fun (((_, attrs), code), pal) =>
         let design := Ir.Design.ofPalette pal
         let paint := s!"background: {HtmlDoc.cssColor design.bg}; color: {HtmlDoc.cssColor design.fg}"
         let keyword := (Listing.ink pal (pal.find? "bg") .keyword).getD design.fg
         attrs.any (fun (key, value) => key == "style" && hasStr value paint) &&
         nodeTextOne "" code == "return value" &&
         (ListingHighlight.coloredSpansOne #[] code).any fun (text, style) =>
           text == "return" && hasStr style (HtmlDoc.cssColor keyword))
    let nested := { doc with body := #[
      .frame #[] standout valign false
        #[.center #[.setPalette dark, code "return value"], .note #[.setPalette light]],
      frame none] }
    let (_, html, _) := HtmlDoc.emitTree {} nested
    let pre := elemAttrsList (· == "pre") #[] html.toList
    t s!"listing epoch {name}: nested palette reaches the next frame, notes do not"
      (pre.size == 2 && pre.all fun (_, attrs) =>
        attrs.any fun (key, value) =>
          key == "style" && hasStr value "background: #000000; color: #ffffff")
    let longCode := String.intercalate "\n" (List.replicate 48 "return value")
    for (epochName, epoch) in [("light", light), ("removed", removed)] do
      let spill := { doc with body := #[.frame #[] standout valign true
          #[.setPalette epoch, .setPalette epoch, code longCode]] }
      let pages := (layoutOf fonts spill).pages
      let ground := epoch.find? "bg"
      t s!"listing epoch {name}/{epochName}: repeated ground reaches every spill page"
        (pages.size ≥ 2 && pages.all fun page =>
          pageGround geom page == ground &&
          (ListingHighlight.glyphColors { pages := #[page], diags := #[] }).any
            (fun (c, color) => c == 'v' && color == (Ir.Design.ofPalette epoch).fg))
      t s!"listing epoch {name}/{epochName}: the fill theorem requires a declared epoch"
        (Layout.pageGroundsDeclared geom fonts none spill == ground.isSome)

/-- The contrast judge must leave a styled frame's entry ground at a body
palette declaration, even an identical one, and retain the authored role's
bounded repair/refusal policy on the new ground. -/
def listingPaletteAuditChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let gray : Ir.Color := { r := 136, g := 136, b := 136 }
  let light := ({} : Ir.Palette).declare "fg" Ir.Color.black
    |>.declare "bg" Ir.Color.white |>.declare "codekeyword" gray
    |>.declare "standoutfg" Ir.Color.white |>.declare "standoutbg" Ir.Color.black
    |>.declare "titlepagefg" Ir.Color.white |>.declare "titlepagebg" Ir.Color.black
  for (name, standout, valign) in
      [("title", false, Ir.VAlign.golden), ("standout", true, .center)] do
    let entry := ListingHighlight.epochDoc light none standout valign
    t s!"listing audit {name}: unchanged entry is judged on its own ground"
      ((Contrast.judgedPairs entry).contains (gray, Ir.Color.black) &&
       (Contrast.docDiags entry).all fun d => !hasStr d.message "'codekeyword'")
    for (epochName, epoch) in [("repeated", light), ("removed", light.erase "bg")] do
      let doc := ListingHighlight.epochDoc light (some epoch) standout valign
      let pairs := (Contrast.judgedPairs doc).filter (·.1 == gray)
      t s!"listing audit {name}/{epochName}: declaration replaces the entry ground"
        (!pairs.isEmpty && pairs.all (·.2 == Ir.Color.white))
      t s!"listing audit {name}/{epochName}: real audit names the current page"
        ((Contrast.docDiags doc).any fun d =>
          d.code == "N0022" && hasStr d.message "'codekeyword'" &&
          hasStr d.message "the page (#FFFFFF)")
    let source := "return value"
    let large := { entry with body := #[.frame #[] standout valign false
      #[.setPalette light, .verbatim none source
        { style := .friendly, fontSize := .size "Huge",
          highlight := ListingHighlight.tokenize .python (Ir.verbatimLines source) }]] }
    t s!"listing audit {name}: epoch reset preserves listing size and authored ink priority"
      ((Contrast.judgedPairs large).contains (gray, Ir.Color.white) &&
       (Contrast.docDiags large).all fun d => !hasStr d.message "'codekeyword'")
    let refused := ListingHighlight.epochDoc light
      (some (light.declare "codekeyword" Ir.Color.white)) standout valign
    t s!"listing audit {name}: an unrepairable authored role still warns"
      ((Contrast.docDiags refused).any fun d =>
        d.code == "W0315" && hasStr d.message "'codekeyword'" &&
        hasStr d.message "the page (#FFFFFF)")
  let code := "\\begin{minted}{python}\nreturn value\n\\end{minted}"
  let preamble := "\\theme{default}\\palette{fg=#000000,bg=#FFFFFF,\
standoutfg=#FFFFFF,standoutbg=#000000}"
  let (continued, _) := elabStr (dvDeck preamble
    ("\\begin{frame}\\palette{fg=#FFFFFF,bg=#000000}" ++ code ++
      "\\end{frame}\\begin{frame}" ++ code ++ "\\end{frame}"))
  let (_, html, _) := HtmlDoc.emitTree {} continued
  let pre := elemAttrsList (· == "pre") #[] html.toList
  t "listing epoch source: both frames ship the declared dark listing pair"
    (pre.size == 2 && pre.all fun (_, attrs) =>
      attrs.any fun (key, value) =>
        key == "style" && hasStr value "background: #000000; color: #ffffff")
  let (repaired, ds) := elabStr (dvDeck preamble
    ("\\begin{frame}[standout]\\palette{bg=#FFFFFF,codekeyword=#888888}" ++
      code ++ "\\end{frame}"))
  let (_, html, _) := HtmlDoc.emitTree {} repaired
  let codes := ListingHighlight.codeNodesList #[] html.toList
  let some ink := Contrast.realize Contrast.aaText Ir.Color.white gray |
    failures ref "listing audit: gray-on-white bounded repair fixture no longer repairs"
  t "listing audit source: the actual audit reports the bounded role repair"
    (ds.any fun d => d.code == "N0022" && hasStr d.message "'codekeyword'" &&
      hasStr d.message "the page (#FFFFFF)")
  t "listing audit source: typed HTML ships the repair on the declared page"
    (Contrast.withinInkBound gray ink &&
     Contrast.contrastMilli ink Ir.Color.white ≥ Contrast.aaText &&
     (elemAttrsList (· == "pre") #[] html.toList).any (fun (_, attrs) =>
       attrs.any fun (key, value) => key == "style" && hasStr value "background: #ffffff") &&
     (ListingHighlight.coloredSpansList #[] codes.toList).any fun (text, style) =>
       text == "return" && hasStr style (HtmlDoc.cssColor ink))

/-- A role repair must reach the run that the audit judged. Every declaration
ends the frame-entry ground, even an identical or nested one; notes do not.
The witnesses read shipped glyphs, PDF paint and the typed HTML spans. -/
def listingRoleEpochChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let gray : Ir.Color := { r := 136, g := 136, b := 136 }
  let some repaired := Contrast.realize Contrast.aaText Ir.Color.white gray |
    failures ref "role epoch: gray-on-white bounded repair fixture no longer repairs"
  let shipped (name : String) (doc : Ir.Doc) (inks grounds : Array Ir.Color) : IO Unit := do
    let out := layoutOf fonts doc
    let glyphs := (ListingHighlight.glyphColors out).filter fun (c, _) =>
      "sample".contains c
    let expected := inks.flatMap fun ink => "sample".toList.toArray.map (·, ink)
    t s!"role epoch {name}: Layout.Out ships the audited ink"
      (glyphs == expected)
    let geom := Layout.Geom.ofPage doc.page
    t s!"role epoch {name}: shipped pages carry the current ground"
      (out.pages.size == grounds.size && (out.pages.zip grounds).all fun (page, ground) =>
        page.fills.any fun fill =>
          fill.x == -geom.bleed && fill.y == -geom.bleed &&
          fill.w == geom.pageW + 2 * geom.bleed &&
          fill.h == geom.pageH + 2 * geom.bleed && fill.color == ground)
    let pdf := pdfText (Pdf.write geom fonts out.pages doc.info)
    t s!"role epoch {name}: emitted PDF paints the audited ink"
      (!inks.isEmpty && inks.all fun ink => bytesContain pdf ink.pdfFill)
    let (_, html, _) := HtmlDoc.emitTree {} doc
    let spans := (ListingHighlight.coloredSpansList #[] html.toList).filter (·.1 == "sample")
    t s!"role epoch {name}: typed HTML carries the audited ink"
      (spans.size == inks.size && (spans.zip inks).all fun ((_, style), ink) =>
        hasStr style (HtmlDoc.cssColor ink))
  let preamble := "\\theme{default}\\palette{fg=#000000,bg=#FFFFFF,accent=#888888,\
standoutfg=#FFFFFF,standoutbg=#000000}"
  for (name, source, ink, code) in
      [("source", "\\textcolor{accent}{sample}", repaired, "N0022"),
       ("large source", "\\Huge\\textcolor{accent}{sample}", Ir.Color.ofHtml 136 136 136, ""),
       ("literal source", "\\textcolor{#888888}{sample}", Ir.Color.ofHtml 136 136 136, "W0315"),
       ("unrepairable source", "\\textcolor{#FFFFFF}{sample}",
         Ir.Color.ofHtml 255 255 255, "W0315")] do
    let (doc, ds) := elabStr (dvDeck preamble
      ("\\begin{frame}[standout]\\palette{bg=#FFFFFF}" ++ source ++ "\\end{frame}"))
    t s!"role epoch {name}: actual audit keeps its repair or refusal policy"
      (ds.all (·.severity != .error) &&
       if code.isEmpty then ds.all (fun d => !hasStr d.message "'accent'")
       else ds.any fun d =>
         d.code == code && hasStr d.message "the page (#FFFFFF)" &&
         (code != "N0022" || (hasStr d.message "'accent'" && hasStr d.message "#767676")))
    shipped name doc #[ink] #[Ir.Color.white]
  let light := ({} : Ir.Palette).declare "fg" Ir.Color.black
    |>.declare "bg" Ir.Color.white |>.declare "accent" gray
    |>.declare "standoutfg" Ir.Color.white |>.declare "standoutbg" Ir.Color.black
    |>.declare "titlepagefg" Ir.Color.white |>.declare "titlepagebg" Ir.Color.black
  let changed := light.declare "alert" Ir.Color.black
  let sample : Ir.Block := .para #[.colored gray (some "accent") #[.text "sample"]]
  let base := { (elabStr (dvDeck "\\theme{default}" "")).1 with palette := light }
  for (frameName, standout, valign) in
      [("title", false, Ir.VAlign.golden), ("standout", true, .center)] do
    for (name, body, count, resets) in
        [("entry", #[sample], 1, false),
         ("notes", #[.note #[.setPalette light], sample], 1, false),
         ("changed", #[.setPalette changed, sample], 1, true),
         ("identical", #[.setPalette light, sample], 1, true),
         ("repeated", #[.setPalette light, .setPalette light, sample], 1, true),
         ("nested", #[.center #[.setPalette light, sample], sample], 2, true),
         ("items", #[.list false #[#[.setPalette light, sample], #[sample]], sample], 3, true),
         ("columns", #[.columns #[(.frac 500, #[.setPalette light, sample]),
           (.frac 500, #[sample])], sample], 3, true),
         ("nested notes", #[.center #[.setPalette light, .note #[.setPalette changed]],
           sample], 1, true)] do
      let raw := { base with body := #[.frame #[] standout valign false body] }
      let (doc, ds) := Contrast.realizeDoc raw
      let name := s!"{frameName}/{name}"
      t s!"role epoch {name}: actual audit names the declared page only after a boundary"
        (if resets then ds.any (fun d =>
          d.code == "N0022" && hasStr d.message "'accent'" &&
          hasStr d.message "the page (#FFFFFF)" && hasStr d.message "#767676")
         else ds.all (fun d => !hasStr d.message "'accent'"))
      shipped name doc (List.replicate count (if resets then repaired else gray)).toArray
        #[if resets then Ir.Color.white else Ir.Color.black]
    let raw := { base with body := #[
      .frame #[] standout valign false #[sample],
      .frame #[] false .center false #[sample]] }
    let (doc, ds) := Contrast.realizeDoc raw
    t s!"role epoch {frameName}/exit: later page repair does not change the entry run"
      (ds.any fun d => d.code == "N0022" && hasStr d.message "'accent'")
    shipped s!"{frameName}/exit" doc #[gray, repaired] #[Ir.Color.black, Ir.Color.white]

/-- Artifact regression: the old pipeline preserves code but ships no syntax
colour in either artifact. These checks must fail on that implementation. -/
def listingHighlightChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  listingLexerChecks ref
  listingFriendlyChecks ref
  let some bytes ← findFont | failures ref "listing highlight: fixture font missing"
  let .ok font := Font.parse bytes | failures ref "listing highlight: fixture font invalid"
  let fonts := oneFaceOf font
  listingPaletteEpochChecks ref fonts
  listingPaletteContinuationChecks ref fonts
  listingPaletteAuditChecks ref
  listingRoleEpochChecks ref fonts
  for (language, source) in [("python", ListingHighlight.pythonSource),
      ("lean4", ListingHighlight.leanSource)] do
    let doc := ListingHighlight.sourceDoc language source
    let (_, body, _) := HtmlDoc.emitTree {} doc
    let codes := ListingHighlight.codeNodesList #[] body.toList
    t s!"highlight {language}: typed HTML preserves code text and whitespace"
      (codes.size == 1 && codes.any fun n => nodeTextOne "" n == source)
    let spans := ListingHighlight.coloredSpansList #[] codes.toList
    t s!"highlight {language}: typed HTML ships colored code spans"
      (spans.size ≥ 3)
    let out := layoutOf fonts doc
    let colored := (ListingHighlight.glyphColors out).filter fun p =>
      p.2 != (Ir.Design.ofDoc doc).fg
    t s!"highlight {language}: shipped PDF glyphs carry syntax colors"
      (colored.size ≥ 3)
    let pdf := pdfText (Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info)
    t s!"highlight {language}: the PDF stream paints the classified ink"
      (!colored.isEmpty && colored.all fun p => bytesContain pdf p.2.pdfFill)
    let expected := [(.keyword, "def"), (.string, "\""), (.number, "2"),
      (.comment, if language == "python" then "#" else "-")]
    for (kind, witness) in expected do
      let some color := Listing.ink doc.palette none kind |
        failures ref s!"highlight {language}: missing class ink {repr kind}"
      t s!"highlight {language}: typed HTML paints class {repr kind}"
        (spans.any fun (text, style) =>
          hasStr text witness && hasStr style (HtmlDoc.cssColor color))
      t s!"highlight {language}: PDF glyphs paint class {repr kind}"
        ((ListingHighlight.glyphColors out).any fun (c, ink) =>
          witness.contains c && ink == color)
  let code := ListingHighlight.pythonSource
  for src in [
      dvDoc "" ("\\begin{lstlisting}[language=Python,numbers=left]\n" ++ code ++
        "\n\\end{lstlisting}"),
      "```python\n" ++ code ++ "\n```"] do
    let doc := if src.startsWith "```" then (elabMd src).1 else (elabStr src).1
    let (_, body, _) := HtmlDoc.emitTree {} doc
    let codes := ListingHighlight.codeNodesList #[] body.toList
    t "highlight listing surfaces: literal code survives numbered listings and markdown"
      (codes.size == 1 && nodeTextOne "" codes[0]! == code &&
       !(ListingHighlight.coloredSpansList #[] codes.toList).isEmpty)
  let plain := ListingHighlight.sourceDoc "unknown-language" code
  let (_, body, _) := HtmlDoc.emitTree {} plain
  let codes := ListingHighlight.codeNodesList #[] body.toList
  t "highlight unknown language: exact plain text, no invented grammar"
    (codes.size == 1 && nodeTextOne "" codes[0]! == code &&
      (ListingHighlight.coloredSpansList #[] codes.toList).isEmpty)
  for theme in Theme.builtin do
    t s!"highlight palette: text AA on every {theme.name} listing ground"
      (Contrast.listingContract theme.palette)
    let standout := { (elabStr (dvDeck ""
        ("\\begin{frame}[standout]\n\\begin{minted}{python}\n" ++ code ++
         "\n\\end{minted}\n\\end{frame}"))).1 with palette := theme.palette }
    let ground := (Ir.Design.ofDoc standout).standout.bg
    let (_, html, _) := HtmlDoc.emitTree {} standout
    let spans := ListingHighlight.coloredSpansList #[]
      (ListingHighlight.codeNodesList #[] html.toList).toList
    let glyphs := ListingHighlight.glyphColors (layoutOf fonts standout)
    let keyword := (Listing.ink theme.palette (some ground) .keyword).getD Ir.Color.black
    t s!"highlight standout: {theme.name} typed HTML projects the local ink"
      (spans.any fun (text, style) =>
        text == "def" && hasStr style (HtmlDoc.cssColor keyword))
    t s!"highlight standout: {theme.name} PDF draws legible local ink"
      (glyphs.any (fun (c, color) => c == 'd' && color == keyword) &&
       glyphs.all (fun (_, color) => Contrast.contrastMilli color ground ≥ Contrast.aaText))
    let doc := { ListingHighlight.sourceDoc "python" "def value(): return \"x\""
      with palette := theme.palette }
    let active := layoutOf fonts doc
    let coveredBody := doc.body.map fun b => match b with
      | .verbatim _ source spec =>
        .verbatim (some (Ir.Design.ofDoc doc).cover.plain) source spec
      | b => b
    let pending := layoutOf fonts { doc with body := coveredBody }
    let activeInk := ListingHighlight.glyphColors active
    let pendingInk := ListingHighlight.glyphColors pending
    t s!"highlight overlay: {theme.name} every token dims using its own ink"
      (activeInk.size > 0 && activeInk.size == pendingInk.size &&
       (activeInk.zip pendingInk).all fun ((c, ink), (c', quiet)) =>
         c == c' && quiet == (Ir.Design.ofDoc doc).cover.of ink)
    let coveredDoc := { doc with
      body := coveredBody
      palette := doc.palette.declare "covered" Ir.Color.black }
    let (_, coveredHtml, _) := HtmlDoc.emitTree {} coveredDoc
    let coveredSpans := ListingHighlight.coloredSpansList #[]
      (ListingHighlight.codeNodesList #[] coveredHtml.toList).toList
    let keyword := (Listing.ink coveredDoc.palette none .keyword).getD Ir.Color.black
    let quiet := (Ir.Design.ofDoc coveredDoc).cover.of keyword
    t s!"highlight overlay: {theme.name} typed HTML keeps literal per-token cover"
      (coveredSpans.any (fun (text, style) =>
         text == "def" && style == s!"color: {HtmlDoc.cssColor quiet}") &&
       coveredSpans.all (fun (_, style) => !hasStr style "var(--covered"))
  let badColor := "\\palette{codekeyword=#FFFFFF}"
  let (_, diagnostics) := elabStr (dvDoc badColor
    "\\begin{minted}{python}\ndef value(): pass\n\\end{minted}")
  t "highlight authored palette: low contrast is judged, not silently replaced"
    (diagnostics.any (·.code == "W0315"))

end Tests
