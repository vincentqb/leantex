module

public import Tests.Support
public import LeanTex.Core.Listing

public section

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

/-- The `#rrggbb` a style declaration's colour ends in: a palette role's
custom property carries the colour as its fallback. -/
def hexIn (css : String) : Option String :=
  match (css.splitOn "#").getLast? with
  | some tail => if (css.splitOn "#").length > 1 then some (String.ofList (tail.toList.take 6)) else none
  | none => none

/-- Each scalar of a code element with the colour, weight and slant it
ships in: the innermost declared colour, and whether a `strong` or `em`
encloses it. -/
abbrev ScalarPaint := Char × Option String × Bool × Bool

mutual

def scalarPaintOne (color : Option String) (bold italic : Bool) (acc : Array ScalarPaint) :
    Html.Node → Array ScalarPaint
  | .text s => s.foldl (fun acc c => acc.push (c, color, bold, italic)) acc
  | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    let own := (attrs.find? fun (key, value) =>
      tag == "span" && key == "style" && hasStr value "color:").bind (hexIn ·.2)
    scalarPaintList (own.or color) (bold || tag == "strong") (italic || tag == "em") acc
      kids.toList

def scalarPaintList (color : Option String) (bold italic : Bool) (acc : Array ScalarPaint) :
    List Html.Node → Array ScalarPaint
  | [] => acc
  | node :: rest => scalarPaintList color bold italic (scalarPaintOne color bold italic acc node) rest

end

/-- The text nodes a tree holds. -/
def textNodesOne : Html.Node → Nat
  | .text _ => 1
  | .elem _ _ kids => textNodesList kids.toList
  | _ => 0
where
  textNodesList : List Html.Node → Nat
    | [] => 0
    | n :: ns => textNodesOne n + textNodesList ns

end ListingHighlight

/-- Listing lines ship as runs of tokens that look alike. Each scalar must
still show its own token's weights, and wherever it lays down ink its own
token's ink, in the typed HTML and in the PDF's glyphs; white space may
take a neighbour's ink, which it does not show. And the runs must cost the
typed tree fewer text nodes than painting token by token would. -/
def listingRunChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let source := "theorem garden (n : Nat) : n + 0 = n := by\n  simp only [Nat.add_zero] -- rows\n" ++
    "def bloom (xs : Array Nat) : Nat := xs[0]! + xs.size"
  for style in [Ir.ListingStyle.default, .friendly] do
    let styleName := if style == .friendly then "friendly" else "default"
    let (doc, _) := elabStr (dvDoc "" ("\\begin{minted}[style=" ++ styleName ++ "]{lean4}\n" ++
      source ++ "\n\\end{minted}"))
    let some (covered, src, spec) := (ListingHighlight.listings doc)[0]?
      | failures ref s!"listing runs {styleName}: no listing"
    let tokens := (spec.tokenLines src).flatten
    let brushOf (k : ListingHighlight.Kind) := Listing.brush doc.palette none covered style k
    let (_, body, _) := emitIn {} doc .print
    let codes := ListingHighlight.codeNodesList #[] body.toList
    let paints := (ListingHighlight.scalarPaintList none false false #[] codes.toList).filter
      (·.1 != '\n')
    let expected : Array ListingHighlight.ScalarPaint := tokens.foldl (fun acc tok =>
      let b := brushOf tok.kind
      let ink := (b.shipsInk tok.text).bind fun (c, _) => ListingHighlight.hexIn (HtmlDoc.cssColor c)
      tok.text.foldl (fun acc c => acc.push (c, ink, b.look.bold, b.look.italic)) acc) #[]
    let shows (p : ListingHighlight.ScalarPaint) :=
      (p.1, if p.1.isWhitespace then none else p.2.1, p.2.2)
    t s!"listing runs {styleName}: every scalar shows its token's weights and ink in typed HTML"
      (!paints.isEmpty && paints.map shows == expected.map shows)
    let nodes := codes.foldl (fun n code => n + ListingHighlight.textNodesOne code) 0
    let lineCount := (spec.tokenLines src).size
    t s!"listing runs {styleName}: runs cost the typed tree fewer text nodes than tokens \
({nodes} for {tokens.size} tokens on {lineCount} lines)"
      (nodes < tokens.size)
    let out := layoutOf fonts doc
    let glyphs := (ListingHighlight.glyphColors out).filter fun (c, _) =>
      !c.isWhitespace && c != '\u00a0'
    let wanted := tokens.foldl (fun acc tok =>
      match (brushOf tok.kind).shipsInk tok.text with
      | some (ink, _) => tok.text.foldl (fun acc c =>
          if c.isWhitespace then acc else acc.push (c, some ink)) acc
      | none => tok.text.foldl (fun acc c => if c.isWhitespace then acc else acc.push (c, none)) acc)
      #[]
    t s!"listing runs {styleName}: every inked glyph keeps its token's ink in the PDF"
      (glyphs.size == wanted.size && (glyphs.zip wanted).all fun ((c, ink), (c', want)) =>
        c == c' && want.all (· == ink))

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
  let friendly := ListingHighlight.Role.all.map fun r =>
    ((CodeColor.resolve {} Ir.Color.white (some .friendly)).get r).map (·.color)
  t "listing friendly: an undeclared palette's roles take the style's sourced colours"
    (friendly == [none, some { r := 0, g := 112, b := 32 }, some { r := 0, g := 112, b := 32 },
      some { r := 64, g := 112, b := 160 }, some { r := 96, g := 160, b := 176 },
      some { r := 255, g := 0, b := 0 }])
  let authored := ({} : Ir.Palette).declare (.role .codeKeyword) Ir.Color.black
  t "listing friendly: authored roles take precedence over style defaults"
    (Listing.ink authored none .keyword (style := some .friendly) == some Ir.Color.black)
  for theme in Theme.builtin do
    let d := Ir.Design.ofPalette (deckBundle theme)
    let grounds := [none, some d.standout.bg] ++
      (d.titlepage.toList.map fun pair => some pair.bg)
    for style in [Ir.ListingStyle.default, .friendly] do
      t s!"listing style: {repr style} text AA on every {theme.name} ground"
        (grounds.all fun ground => Listing.contract (deckBundle theme) ground (style := some style))
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
  let (_, defaultHtml, _) := emitIn {} defaultDoc .print
  let (_, friendlyHtml, _) := emitIn {} friendlyDoc .print
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
    let (_, html, _) := emitIn {} doc .print
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

/-- The native lexers are Pygments' own (`pygmentsLexerChecks` holds every
recorded stream token for token); these pins name what a reader sees: a
proof hole, a declaration, a decorator, an interpolation, a prompt. The IR's
reader stays honest on what no lexer vouches for: stale classification. -/
def listingLexerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let lean := ListingHighlight.classified .lean4
    "@[simp] theorem t : 1 = 1 := by\n  sorry\n/- outer /- nested -/ -/ #eval `name"
  t "highlight lexer: Lean attributes, declarations and proof holes take Pygments' types"
    (ListingHighlight.hasToken lean ⟨"Keyword.Declaration"⟩ "@[" &&
     ListingHighlight.hasToken lean ⟨"Keyword.Namespace"⟩ "theorem" &&
     ListingHighlight.hasToken lean .genericError "sorry" &&
     ListingHighlight.hasToken lean ⟨"Literal.String.Symbol"⟩ "`name")
  t "highlight lexer: a nested Lean comment closes where Lean closes it"
    (ListingHighlight.hasToken lean .comment "/-" &&
     ListingHighlight.hasToken lean ⟨"Comment.Multiline"⟩ " outer /- nested -/ -/")
  let python := ListingHighlight.classified .python
    "@cache\ndef area(r):\n    return f\"{r!r:>4}\" + str(3.5e2)  # done"
  t "highlight lexer: Python decorators, functions, interpolation and literals"
    (ListingHighlight.hasToken python ⟨"Name.Decorator"⟩ "@cache" &&
     ListingHighlight.hasToken python .nameFunction "area" &&
     ListingHighlight.hasToken python ⟨"Literal.String.Interpol"⟩ "!r:" &&
     ListingHighlight.hasToken python .nameBuiltin "str" &&
     ListingHighlight.hasToken python ⟨"Literal.Number.Float"⟩ "3.5e2" &&
     ListingHighlight.hasToken python ⟨"Comment.Single"⟩ "# done")
  let session := ListingHighlight.classified .console "$ echo hi\nhi\n# whoami\nroot"
  t "highlight lexer: a shell session's prompts, commands and output"
    (ListingHighlight.hasToken session ⟨"Generic.Prompt"⟩ "$ " &&
     ListingHighlight.hasToken session .nameBuiltin "echo" &&
     ListingHighlight.hasToken session ⟨"Generic.Output"⟩ "hi" &&
     ListingHighlight.hasToken session ⟨"Generic.Prompt"⟩ "# ")
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
  -- Inks with a hue of their own, so a keyword derives a tone of its own.
  let light := ({} : Ir.Palette).declare (.role .ink) (Ir.Color.ofHtml 0x1F 0x2B 0x4D)
    |>.declare (.role .page) Ir.Color.white
    |>.declare (.role .standoutInk) Ir.Color.white |>.declare (.role .standoutGround) Ir.Color.black
    |>.declare (.role .titlePageInk) Ir.Color.white |>.declare (.role .titlePageGround) Ir.Color.black
  let dark := light.declare (.role .ink) (Ir.Color.ofHtml 0xC8 0xD8 0xF8) |>.declare (.role .page) Ir.Color.black
  let removed := { light with
    entries := light.entries.filter fun (role, _) => role != .role .ink && role != .role .page }
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
      -- The PDF is the printed page: the typed tree as print reads it. A
      -- deck whose page is dark ships its dark screen, whose own class
      -- defaults stand where an epoch removes its colours.
      let (_, html, _) := emitIn {} doc .print
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
  -- Inks with a hue of their own, so a keyword derives a tone of its own.
  let light := ({} : Ir.Palette).declare (.role .ink) (Ir.Color.ofHtml 0x1F 0x2B 0x4D)
    |>.declare (.role .page) Ir.Color.white
    |>.declare (.role .standoutInk) Ir.Color.white |>.declare (.role .standoutGround) Ir.Color.black
    |>.declare (.role .titlePageInk) Ir.Color.white |>.declare (.role .titlePageGround) Ir.Color.black
  let dark := light.declare (.role .ink) (Ir.Color.ofHtml 0xC8 0xD8 0xF8) |>.declare (.role .page) Ir.Color.black
  let removed := light.erase (.role .page)
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
    let (_, html, _) := emitIn {} doc .print
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
    let (_, html, _) := emitIn {} nested .print
    let pre := elemAttrsList (· == "pre") #[] html.toList
    t s!"listing epoch {name}: nested palette reaches the next frame, notes do not"
      (pre.size == 2 && pre.all fun (_, attrs) =>
        attrs.any fun (key, value) =>
          key == "style" && hasStr value
            s!"background: #000000; color: {HtmlDoc.cssColor (Ir.Design.ofPalette dark).fg}")
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
palette declaration, even an identical one, and report the authored role's
pairing on the new ground. The grey fails even the large-scale ratio a
deck's stage-size text asks, so the pairing is reported. -/
def listingPaletteAuditChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let gray : Ir.Color := { r := 0xAA, g := 0xAA, b := 0xAA }
  let light := ({} : Ir.Palette).declare (.role .ink) Ir.Color.black
    |>.declare (.role .page) Ir.Color.white |>.declare (.role .codeKeyword) gray
    |>.declare (.role .standoutInk) Ir.Color.white |>.declare (.role .standoutGround) Ir.Color.black
    |>.declare (.role .titlePageInk) Ir.Color.white |>.declare (.role .titlePageGround) Ir.Color.black
  for (name, standout, valign) in
      [("title", false, Ir.VAlign.golden), ("standout", true, .center)] do
    let entry := ListingHighlight.epochDoc light none standout valign
    t s!"listing audit {name}: unchanged entry is judged on its own ground"
      ((Contrast.judgedPairs entry).contains (gray, Ir.Color.black) &&
       (Contrast.docDiags entry).all fun d => !hasStr d.message "'codekeyword'")
    for (epochName, epoch) in [("repeated", light), ("removed", light.erase (.role .page))] do
      let doc := ListingHighlight.epochDoc light (some epoch) standout valign
      let pairs := (Contrast.judgedPairs doc).filter (·.1 == gray)
      t s!"listing audit {name}/{epochName}: declaration replaces the entry ground"
        (!pairs.isEmpty && pairs.all (·.2 == Ir.Color.white))
      t s!"listing audit {name}/{epochName}: real audit names the current page"
        ((Contrast.docDiags doc).any fun d =>
          d.code == "W0315" && hasStr d.message "'codekeyword'" &&
          d.detail.any (hasStr · "on #FFFFFF"))
    let source := "return value"
    let large := { entry with body := #[.frame #[] standout valign false
      #[.setPalette light, .verbatim none source
        { style := some .friendly, fontSize := .size "Huge",
          highlight := ListingHighlight.tokenize .python (Ir.verbatimLines source) }]] }
    t s!"listing audit {name}: epoch reset preserves listing size and authored ink priority"
      ((Contrast.judgedPairs large).contains (gray, Ir.Color.white) &&
       (Contrast.docDiags large).any fun d =>
         hasStr d.message "'codekeyword'" && hasStr d.message "large-scale text")
    let refused := ListingHighlight.epochDoc light
      (some (light.declare (.role .codeKeyword) Ir.Color.white)) standout valign
    t s!"listing audit {name}: an unrepairable authored role still warns"
      ((Contrast.docDiags refused).any fun d =>
        d.code == "W0315" && hasStr d.message "'codekeyword'" &&
        d.detail.any (hasStr · "on #FFFFFF"))
  let code := "\\begin{minted}{python}\nreturn value\n\\end{minted}"
  let preamble := "\\theme{default}\\palette{fg=#000000,bg=#FFFFFF,\
standoutfg=#FFFFFF,standoutbg=#000000}"
  let (continued, _) := elabStr (dvDeck preamble
    ("\\begin{frame}\\palette{fg=#FFFFFF,bg=#000000}" ++ code ++
      "\\end{frame}\\begin{frame}" ++ code ++ "\\end{frame}"))
  let (_, html, _) := emitIn {} continued .print
  let pre := elemAttrsList (· == "pre") #[] html.toList
  t "listing epoch source: both frames ship the declared dark listing pair"
    (pre.size == 2 && pre.all fun (_, attrs) =>
      attrs.any fun (key, value) =>
        key == "style" && hasStr value "background: #000000; color: #ffffff")
  let (declared, ds) := elabStr (dvDeck preamble
    ("\\begin{frame}[standout]\\palette{bg=#FFFFFF,codekeyword=#AAAAAA}" ++
      code ++ "\\end{frame}"))
  let (_, html, _) := emitIn {} declared .print
  let codes := ListingHighlight.codeNodesList #[] html.toList
  t "listing audit source: the actual audit reports the role's pairing on the page"
    (ds.any fun d => d.code == "W0315" && hasStr d.message "'codekeyword'" &&
      d.detail.any (hasStr · "on #FFFFFF"))
  t "listing audit source: typed HTML ships the declared ink on the declared page"
    ((elemAttrsList (· == "pre") #[] html.toList).any (fun (_, attrs) =>
       attrs.any fun (key, value) => key == "style" && hasStr value "background: #ffffff") &&
     (ListingHighlight.coloredSpansList #[] codes.toList).any fun (text, style) =>
       text == "return" && hasStr style (HtmlDoc.cssColor gray))

/-- The pair the audit reports is the pair the run ships: the declared ink, on
the ground the audit judged. Every declaration ends the frame-entry ground,
even an identical or nested one; notes do not. The witnesses read shipped
glyphs, PDF paint and the typed HTML spans. The grey fails even the
large-scale ratio a deck's stage-size text asks. -/
def listingRoleEpochChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let gray : Ir.Color := { r := 0xAA, g := 0xAA, b := 0xAA }
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
    let (_, html, _) := emitIn {} doc .print
    let spans := (ListingHighlight.coloredSpansList #[] html.toList).filter (·.1 == "sample")
    t s!"role epoch {name}: typed HTML carries the audited ink"
      (spans.size == inks.size && (spans.zip inks).all fun ((_, style), ink) =>
        hasStr style (HtmlDoc.cssColor ink))
  let preamble := "\\theme{default}\\palette{fg=#000000,bg=#FFFFFF,accent=#AAAAAA,\
standoutfg=#FFFFFF,standoutbg=#000000}"
  for (name, source, ink) in
      [("source", "\\textcolor{accent}{sample}", Ir.Color.ofHtml 0xAA 0xAA 0xAA),
       ("literal source", "\\textcolor{#AAAAAA}{sample}", Ir.Color.ofHtml 0xAA 0xAA 0xAA),
       ("white source", "\\textcolor{#FFFFFF}{sample}", Ir.Color.ofHtml 255 255 255)] do
    let (doc, ds) := elabStr (dvDeck preamble
      ("\\begin{frame}[standout]\\palette{bg=#FFFFFF}" ++ source ++ "\\end{frame}"))
    t s!"role epoch {name}: actual audit reports the pairing on the declared page"
      (ds.all (·.severity != .error) &&
       ds.any fun d =>
         d.code == "W0315" && d.detail.any (hasStr · "on #FFFFFF") &&
         (name != "source" || hasStr d.message "'accent'"))
    shipped name doc #[ink] #[Ir.Color.white]
  let light := ({} : Ir.Palette).declare (.role .ink) Ir.Color.black
    |>.declare (.role .page) Ir.Color.white |>.declare (.color "accent") gray
    |>.declare (.role .standoutInk) Ir.Color.white |>.declare (.role .standoutGround) Ir.Color.black
    |>.declare (.role .titlePageInk) Ir.Color.white |>.declare (.role .titlePageGround) Ir.Color.black
  let changed := light.declare (.role .alert) Ir.Color.black
  let sample : Ir.Block := .para #[.colored gray (some (.color "accent")) #[.text "sample"]]
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
      let doc := { base with body := #[.frame #[] standout valign false body] }
      let ds := Contrast.docDiags doc
      let name := s!"{frameName}/{name}"
      t s!"role epoch {name}: actual audit names the declared page only after a boundary"
        (if resets then ds.any (fun d =>
          d.code == "W0315" && hasStr d.message "'accent'" &&
          d.detail.any (hasStr · "on #FFFFFF"))
         else ds.all (fun d => !hasStr d.message "'accent'"))
      shipped name doc (List.replicate count gray).toArray
        #[if resets then Ir.Color.white else Ir.Color.black]
    let doc := { base with body := #[
      .frame #[] standout valign false #[sample],
      .frame #[] false .center false #[sample]] }
    let ds := Contrast.docDiags doc
    t s!"role epoch {frameName}/exit: the later page's pairing is reported, the entry run kept"
      (ds.any fun d => d.code == "W0315" && hasStr d.message "'accent'")
    shipped s!"{frameName}/exit" doc #[gray, gray] #[Ir.Color.black, Ir.Color.white]

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
  listingRunChecks ref fonts
  for (language, source) in [("python", ListingHighlight.pythonSource),
      ("lean4", ListingHighlight.leanSource)] do
    let doc := ListingHighlight.sourceDoc language source
    let (_, body, _) := emitIn {} doc .print
    let codes := ListingHighlight.codeNodesList #[] body.toList
    t s!"highlight {language}: typed HTML preserves code text and whitespace"
      (codes.size == 1 && codes.any fun n => nodeTextOne "" n == source)
    let spans := ListingHighlight.coloredSpansList #[] codes.toList
    t s!"highlight {language}: typed HTML ships colored code spans"
      (spans.size ≥ 3)
    -- White space lays down no ink: its type's colour would only cost a span.
    t s!"highlight {language}: no coloured span holds only white space"
      (spans.all fun (text, _) => !text.all Char.isWhitespace)
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
    let (_, body, _) := emitIn {} doc .print
    let codes := ListingHighlight.codeNodesList #[] body.toList
    t "highlight listing surfaces: literal code survives numbered listings and markdown"
      (codes.size == 1 && nodeTextOne "" codes[0]! == code &&
       !(ListingHighlight.coloredSpansList #[] codes.toList).isEmpty)
  let plain := ListingHighlight.sourceDoc "unknown-language" code
  let (_, body, _) := emitIn {} plain .print
  let codes := ListingHighlight.codeNodesList #[] body.toList
  t "highlight unknown language: exact plain text, no invented grammar"
    (codes.size == 1 && nodeTextOne "" codes[0]! == code &&
      (ListingHighlight.coloredSpansList #[] codes.toList).isEmpty)
  for theme in Theme.builtin do
    t s!"highlight palette: text AA on every {theme.name} listing ground"
      (Contrast.listingContract (deckBundle theme))
    let standout := { (elabStr (dvDeck ""
        ("\\begin{frame}[standout]\n\\begin{minted}{python}\n" ++ code ++
         "\n\\end{minted}\n\\end{frame}"))).1 with palette := deckBundle theme }
    let ground := (Ir.Design.ofDoc standout).standout.bg
    let (_, html, _) := emitIn {} standout .print
    let spans := ListingHighlight.coloredSpansList #[]
      (ListingHighlight.codeNodesList #[] html.toList).toList
    let glyphs := ListingHighlight.glyphColors (layoutOf fonts standout)
    let literal := (Listing.ink (deckBundle theme) (some ground) .string).getD Ir.Color.black
    t s!"highlight standout: {theme.name} typed HTML projects the local ink"
      (spans.any fun (text, style) =>
        text.trimAscii.toString == "\"hello\"" && hasStr style (HtmlDoc.cssColor literal))
    t s!"highlight standout: {theme.name} PDF draws legible local ink"
      (glyphs.any (fun (c, color) => c == 'h' && color == literal) &&
       glyphs.all (fun (_, color) => Contrast.contrastMilli color ground ≥ Contrast.aaText))
    let doc := { ListingHighlight.sourceDoc "python" "def value(): return \"x\""
      with palette := deckBundle theme }
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
      palette := doc.palette.declare (.role .covered) Ir.Color.black }
    let (_, coveredHtml, _) := emitIn {} coveredDoc .print
    let coveredSpans := ListingHighlight.coloredSpansList #[]
      (ListingHighlight.codeNodesList #[] coveredHtml.toList).toList
    let literal := (Listing.ink coveredDoc.palette none .string).getD Ir.Color.black
    let quiet := (Ir.Design.ofDoc coveredDoc).cover.of literal
    t s!"highlight overlay: {theme.name} typed HTML keeps literal per-token cover"
      (coveredSpans.any (fun (text, style) =>
         text.trimAscii.toString == "\"x\"" &&
           lightStyle [] style == s!"color: {HtmlDoc.cssColor quiet}") &&
       coveredSpans.all (fun (_, style) => !hasStr style "var(--covered"))
  let badColor := "\\palette{codekeyword=#FFFFFF}"
  let (_, diagnostics) := elabStr (dvDoc badColor
    "\\begin{minted}{python}\ndef value(): pass\n\\end{minted}")
  t "highlight authored palette: low contrast is judged, not silently replaced"
    (diagnostics.any (·.code == "W0315"))

end Tests
