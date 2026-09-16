import LeanTex.Core.Html
import LeanTex.Core.Ir
import LeanTex.Core.Dim

namespace LeanTex.Core.HtmlDoc

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Dim LeanTex.Core.Html

/-- How much CSS to emit, and whose class names to use. -/
inductive CssMode where
  /-- Our own token-driven stylesheet, inlined. Self-contained by default: no
  CDN, no webfont round-trip, works offline. -/
  | own
  /-- Bulma class names plus a `--bulma-*` binding of our tokens, for pages
  that drop into an existing Bulma site. The framework itself is not shipped;
  the host page provides it. -/
  | bulma
  /-- Semantic markup only. Bring your own stylesheet. -/
  | none
  deriving Repr, BEq

structure Config where
  css : CssMode := .own
  lang : String := "en"
  /-- Optional client-side math renderer, used until native MathML lands.
  A boundary, not a dependency: nothing is emitted unless asked for. -/
  mathBoundary : Option String := none
  deriving Repr

private def hex2 (v : UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[v.toNat / 16]!, d[v.toNat % 16]!]

def cssColor (c : Color) : String := s!"#{hex2 c.r}{hex2 c.g}{hex2 c.b}"

/-- A length in CSS. `em`/`ex` survive as their CSS equivalents rather than
being resolved, so the browser scales them with the reader's font size — the
one place HTML should *not* copy what the PDF path does. -/
def cssLength (l : Length) : String :=
  let parts :=
    (if l.sp != 0 then [s!"{l.sp.toPtString}pt"] else []) ++
    (if l.em != 0 then [s!"{(l.em / 10)}%"] else []) ++
    (if l.ex != 0 then [s!"calc({l.ex} * 0.001em * 0.52)"] else [])
  match parts with
  | [] => "0"
  | [one] => one
  | many => "calc(" ++ String.intercalate " + " many ++ ")"

/-- Design tokens become CSS custom properties, so the same declarations drive
both backends and a reader's stylesheet can override them. -/
def tokenVars (doc : Doc) : String :=
  let palette := doc.palette.entries.toList.map fun (n, c) =>
    s!"    --{n}: {cssColor c};"
  let tokens := doc.tokens.entries.toList.map fun (n, g) =>
    s!"    --{n}: {cssLength g.width};"
  let fonts :=
    (match doc.fonts.body with
     | some f => [s!"    --font-body: \"{f}\", Georgia, serif;"]
     | none => []) ++
    (match doc.fonts.sans with
     | some f => [s!"    --font-sans: \"{f}\", system-ui, sans-serif;"]
     | none => []) ++
    (match doc.fonts.mono with
     | some f => [s!"    --font-mono: \"{f}\", ui-monospace, monospace;"]
     | none => [])
  String.intercalate "\n" (palette ++ tokens ++ fonts)

/-- The base stylesheet. Small on purpose: a generated document should not
ship a framework to use four of its rules. Dark mode is a variant of the same
token set, not an inversion hack. -/
def baseCss (doc : Doc) : String :=
  ":root {\n" ++
  "    color-scheme: light dark;\n" ++
  "    --measure: 68ch;\n" ++
  "    --ink: #18181b;\n" ++
  "    --surface: #fafaf9;\n" ++
  "    --muted: #71717a;\n" ++
  "    --accent: #1d4ed8;\n" ++
  "    --tint: #f4f4f5;\n" ++
  "    --rule: #e4e4e7;\n" ++
  "    --font-body: Georgia, \"Times New Roman\", serif;\n" ++
  "    --font-sans: system-ui, -apple-system, \"Segoe UI\", sans-serif;\n" ++
  "    --font-mono: ui-monospace, SFMono-Regular, Menlo, monospace;\n" ++
  tokenVars doc ++ "\n" ++
  "}\n" ++
  "@media (prefers-color-scheme: dark) {\n" ++
  "  :root {\n" ++
  "    --ink: #fafaf9;\n" ++
  "    --surface: #18181b;\n" ++
  "    --muted: #a1a1aa;\n" ++
  "    --tint: #27272a;\n" ++
  "    --rule: #3f3f46;\n" ++
  "  }\n" ++
  "}\n" ++
  "*, *::before, *::after { box-sizing: border-box; }\n" ++
  "body {\n" ++
  "  margin: 0;\n" ++
  "  padding: 2.5rem 1.25rem 4rem;\n" ++
  "  background: var(--surface);\n" ++
  "  color: var(--ink);\n" ++
  "  font-family: var(--font-body);\n" ++
  "  font-size: 1.0625rem;\n" ++
  "  line-height: 1.55;\n" ++
  "  text-rendering: optimizeLegibility;\n" ++
  "  -webkit-font-smoothing: antialiased;\n" ++
  "}\n" ++
  "main { max-width: var(--measure); margin: 0 auto; }\n" ++
  "h1, h2, h3, h4 {\n" ++
  "  font-family: var(--font-sans);\n" ++
  "  font-weight: 600;\n" ++
  "  line-height: 1.2;\n" ++
  "  margin: 2.25rem 0 0.6rem;\n" ++
  "  text-wrap: balance;\n" ++
  "}\n" ++
  "h1 { font-size: 1.9rem; margin-top: 0; }\n" ++
  "h2 { font-size: 1.45rem; }\n" ++
  "h3 { font-size: 1.2rem; }\n" ++
  "p { margin: 0 0 1rem; }\n" ++
  "ul, ol { margin: 0 0 1rem; padding-left: 1.35rem; }\n" ++
  "li { margin: 0.25rem 0; }\n" ++
  "li::marker { color: var(--muted); }\n" ++
  "a { color: var(--accent); text-decoration-thickness: 1px;\n" ++
  "    text-underline-offset: 2px; }\n" ++
  "a:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }\n" ++
  "code, pre { font-family: var(--font-mono); font-size: 0.925em; }\n" ++
  "pre { background: var(--tint); padding: 0.9rem 1rem; overflow-x: auto;\n" ++
  "      border-radius: 4px; }\n" ++
  ".centered { text-align: center; }\n" ++
  ".fill { flex: 1 1 auto; }\n" ++
  ".spaced { margin-top: var(--sep, 1.4rem); }\n" ++
  ".entry { display: flex; flex-wrap: wrap; gap: 0.4rem; align-items: baseline; }\n" ++
  ".math { font-family: \"Latin Modern Math\", \"STIX Two Math\", math; }\n" ++
  "@media print {\n" ++
  "  body { background: #fff; color: #000; padding: 0; }\n" ++
  "  a { color: inherit; }\n" ++
  "}\n" ++
  "@media (prefers-reduced-motion: reduce) {\n" ++
  "  * { animation: none !important; transition: none !important; }\n" ++
  "}"

private def styleClass : Style → String
  | .bold => "b"
  | .italic => "i"
  | .mono => "mono"
  | .smallcaps => "sc"
  | .emph => "em"
  | .sans => "sans"
  | .normal => "normal"
  | .size n => "size-" ++ n

/-- Inline content. Style maps onto the element that carries the *meaning*
where one exists (`<strong>`, `<em>`, `<code>`) and onto a class otherwise. -/
partial def inlineNode (cfg : Config) (x : Inline) : Array Node :=
  match x with
  | .text s => #[Html.text s]
  | .math display src =>
    -- Until native MathML lands the source rides in a data attribute, so an
    -- optional client-side renderer can find it and nothing is faked.
    let tag := if display then "div" else "span"
    #[Html.elem tag #[Html.text src]
        #[("class", if display then "math math-display" else "math"),
          ("data-tex", src)]]
  | .styled st body =>
    let kids := body.flatMap (inlineNode cfg)
    match st with
    | .bold => #[Html.elem "strong" kids]
    | .italic => #[Html.elem "em" kids]
    | .emph => #[Html.elem "em" kids]
    | .mono => #[Html.elem "code" kids]
    | .normal => kids
    | other => #[Html.elem "span" kids #[("class", styleClass other)]]
  | .colored c name body =>
    -- A named colour becomes a custom-property reference with the literal as
    -- fallback, so the token really is the styling API: a host page can
    -- restyle the document by redefining --primary.
    let value := match name with
      | some n => s!"color: var(--{n}, {cssColor c})"
      | none => s!"color: {cssColor c}"
    #[Html.elem "span" (body.flatMap (inlineNode cfg)) #[("style", value)]]
  | .link url body =>
    #[Html.elem "a" (body.flatMap (inlineNode cfg)) #[("href", url)]]
  | .fill => #[Html.elem "span" #[] #[("class", "fill")]]
  -- Page furniture has no meaning in a continuous document.
  | .pageNumber => #[]
  | .pageCount => #[]
  | .linebreak extra =>
    -- Extra space after a break is vertical, so it is a sized block rather
    -- than a second <br>: a doubled <br> would depend on line-height.
    if extra == ({} : SymGlue) then #[Html.elem "br" #[]]
    else #[Html.elem "br" #[],
      Html.elem "span" #[]
        #[("style", s!"display:block;height:{cssLength extra.width}")]]

private def inlines (cfg : Config) (xs : Array Inline) : Array Node :=
  xs.flatMap (inlineNode cfg)

/-- Does this paragraph use `\hfill`? If so it becomes a flex row, which is
the CSS equivalent of the stretch it asked for. -/
private def hasFill (xs : Array Inline) : Bool :=
  xs.any fun x => match x with
    | .fill => true
    | _ => false

partial def blockNode (cfg : Config) (b : Block) : Node :=
  match b with
  | .para content =>
    let attrs := if hasFill content then #[("class", "entry")] else #[]
    Html.elem "p" (inlines cfg content) attrs
  | .section level _ title =>
    let tag := match level with
      | 1 => "h2"
      | 2 => "h3"
      | _ => "h4"
    Html.elem tag (inlines cfg title)
  | .list ordered items =>
    let tag := if ordered then "ol" else "ul"
    Html.elem tag (items.map fun item =>
      -- A one-paragraph item carries its content directly: wrapping it in <p>
      -- is what makes generated lists render with extra vertical space.
      if item.size == 1 then
        match item[0]! with
        | .para content => Html.elem "li" (inlines cfg content)
        | other => Html.elem "li" #[blockNode cfg other]
      else
        Html.elem "li" (item.map (blockNode cfg)))
  | .center body =>
    Html.elem "div" (body.map (blockNode cfg)) #[("class", "centered")]
  | .spaced before body =>
    let style := s!"margin-top: {cssLength before.width}"
    Html.elem "div" (body.map (blockNode cfg)) #[("class", "spaced"), ("style", style)]

/-- Emit a document. Returns the file and any diagnostics the backend itself
raises — running content is the notable one: page furniture cannot be honoured
in a continuous document, and dropping it silently would be the kind of quiet
failure this engine exists to avoid. -/
def emit (cfg : Config) (doc : Doc) : String × Array Diag := Id.run do
  let mut diags : Array Diag := #[]
  if doc.head.isSome || doc.foot.isSome then
    diags := diags.push {
      severity := .warning
      code := "W0007"
      message := "running head/foot is paged-media furniture; omitted from HTML"
      help := some "put a masthead in the document body if it should appear in both"
    }
  let title := doc.info.title.getD "Untitled"
  let mut head : Array Node := #[
    Html.elem "meta" #[] #[("charset", "utf-8")],
    Html.elem "meta" #[] #[("name", "viewport"),
      ("content", "width=device-width, initial-scale=1")],
    Html.elem "title" #[Html.text title]
  ]
  for (name, value) in [("author", doc.info.author), ("description", doc.info.subject),
      ("keywords", doc.info.keywords)] do
    if let some v := value then
      head := head.push (Html.elem "meta" #[] #[("name", name), ("content", v)])
  head := head.push (Html.elem "meta" #[] #[("name", "generator"), ("content", "leantex")])
  match cfg.css with
  | .own => head := head.push (Node.style (baseCss doc))
  | .bulma =>
    -- Bind our tokens onto Bulma's own custom properties so a host page's
    -- theme and ours agree instead of fighting.
    head := head.push (Node.style (":root {\n" ++ tokenVars doc ++ "\n" ++
      "    --bulma-primary: var(--primary, var(--accent, #1d4ed8));\n" ++
      "    --bulma-link: var(--accent, #1d4ed8);\n" ++
      "    --bulma-body-family: var(--font-body, inherit);\n" ++
      "}"))
  | .none => pure ()
  let bodyClass := match cfg.css with
    | .bulma => "content"
    | _ => ""
  let inner := doc.body.map (blockNode cfg)
  let main := Html.elem "main" inner (if bodyClass.isEmpty then #[]
    else #[("class", bodyClass)])
  let mut body : Array Node := #[main]
  if let some tool := cfg.mathBoundary then
    body := body.push (Html.elem "script" #[]
      #[("data-math-boundary", tool), ("src", tool)])
  return (Html.document cfg.lang head body, diags)

end LeanTex.Core.HtmlDoc
