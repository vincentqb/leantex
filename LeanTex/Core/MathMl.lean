import LeanTex.Core.Html
import LeanTex.Core.Math

/-! Math on the HTML backend: MathML Core, emitted from the parsed math AST
the PDF lays out — one parser, two projections (PLAN, M6). MathML Core
(W3C CR, 2025-06-24, w3.org/TR/mathml-core) is the declarative floor: no
script is emitted, and the `--math-boundary` client renderer stays the
opt-in that may replace the element it finds by `data-tex`.

Every leaf goes through the typed tree, so author text reaches the page
only through the certified escaper. `mathml_glyphs_agree` is the census:
the text content of the emission — which lives only in the `mi`/`mn`/`mo`
token leaves — equals `listChars`, the pure glyph-text fold over the same
AST, exposed here because the PDF's own glyph walk (`Layout.layMathTail`)
is private and entangled with font metrics; the fold's agreement with the
PDF's coverage census (`Math.MList.scalarsList`) is held by test
(`mathmlChecks`), overline excepted and stated there. -/

namespace LeanTex.Core.MathMl

open LeanTex.Core LeanTex.Core.Math

/-- One scalar as the string a token leaf carries. -/
def charText (c : Char) : String := String.ofList [c]

/-- The overline operator the U+0305 accent renders as: U+203E OVERLINE,
a postfix stretchy operator with inline intrinsic stretch axis in MathML
Core's operator dictionary (§B.1 category I; §B.3 maps U+0305 combining
overline to it) — where the PDF draws the same accent as a rule from the
overbar constants. -/
def overlineChar : Char := '\u203E'

/-- The token element a lone scalar sets in, by its TeX class: operator
classes are `mo` (MathML Core §3.2.4 — fences, separators and accents
included); an Ord or Inner scalar is `mn` for a digit and `mi` otherwise
(§3.2.2, §3.2.3). -/
def leafTag (cls : MathClass) (c : Char) : String :=
  match cls with
  | .op | .bin | .rel | .opening | .closing | .punct => "mo"
  | .ord | .inner => if c.isDigit then "mn" else "mi"

/-- A measured coordinate divided by its provider's em. Six decimal places
bound serialization error by half a millionth of that em; the integer SVG
points themselves lose no precision. This is decimal serialization, not a
font-size or attachment constant. -/
def measuredEm (n em : Int) : String :=
  let d := (max 1 em).toNat
  let m := (n.natAbs * 1000000 + d / 2) / d
  let fs := toString (m % 1000000)
  (if n < 0 && m != 0 then "-" else "") ++
    s!"{m / 1000000}." ++ "".pushn '0' (6 - fs.length) ++ fs ++ "em"

/-- Signed mu over 18ths of the current em (TeXbook p. 168).
Negative spacing is emitted as an inline margin: MathML Core §3.2.5's
width hint rejects negative values, whereas CSS margins preserve the
following glyph displacement and the row's advance. -/
def muWidth (mu : Int) : String := measuredEm mu 18

/-- The padding a stretched array's cells add above and below, so its rows
stand `\arraystretch` times the one-baseline pitch apart: half the stretch
past one, of the 1.2 em baseline the PDF assembly reads (`leadingFor`), on
top of MathML Core's default 0.5ex. `none` at the default stretch. -/
def stretchPad (stretch : Nat) : Option String :=
  if stretch ≤ 1000 then none else
    let m := (stretch - 1000) * 6 / 10
    let fs := toString (m % 1000)
    let em := s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "em"
    some s!"padding-top: calc(0.5ex + {em}); padding-bottom: calc(0.5ex + {em})"

/-- A `\left`/`\right` delimiter: stretchy, and symmetric about the math
axis (`mo` attributes, MathML Core §3.2.4.2) — rule 19's centring, which
`Layout.delimAssemble` realizes on the PDF side. -/
def delimMo (c : Char) : Html.Node :=
  .elem "mo" #[("stretchy", "true"), ("symmetric", "true")]
    #[.text (charText c)]

/-- A `\genfrac` delimiter: stretched to exactly `size`, amsmath's fixed
delimiter size rather than the content's reach (`minsize` and `maxsize`
clamp an operator's stretch, MathML Core §3.2.4.2), as
`Layout.delimAssembleTo` grows the PDF's. -/
def sizedMo (c : Char) (size : String) : Html.Node :=
  .elem "mo" #[("stretchy", "true"), ("symmetric", "true"), ("minsize", size),
    ("maxsize", size)] #[.text (charText c)]

/-- The size an amsmath sized delimiter stretches to, in em: the PDF's own
target (`Math.bigTarget`) for a face whose `(` is one em tall and deep, to
the thousandth. The `\vcenter` itself (1.2 em at `\big`) is not the target:
Chromium stretches to the variant nearest it, one step past TeX's at
`\big` (1.195 em against 1.094 em in Latin Modern Math). -/
def bigMoSize (step : Nat) : String :=
  let t := (Math.bigTarget 1000 1000 step).toNat
  let frac := ((toString (1000 + t % 1000)).drop 1).toString
  s!"{t / 1000}.{frac}em"

/-- A fraction's declared rule as `mfrac`'s `linethickness` (MathML Core
§3.3.2). The measured em carries physical lengths into the same responsive
coordinate system as glyphs and attachments. A caller without font metrics
keeps the physical length; an undeclared rule belongs to the face. -/
def ruleAttrs (rule : Option Int) (em : Option Int) : Array (String × String) :=
  match rule with
  | none => #[]
  | some t =>
    let width := max t 0
    let length := match em with
      | some size => if 0 < size then measuredEm width size else points width
      | none => points width
    #[("linethickness", length)]
where
  points (width : Int) : String :=
    let m := width * 1000 / 65536
    let fs := toString (m % 1000)
    if m == 0 then "0"
    else s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "pt"

/-- A style switch as MathML Core's `displaystyle` and absolute
`scriptlevel` (§2.1.6): `\displaystyle`, `\textstyle`, `\scriptstyle` and
`\scriptscriptstyle` set a style, never a step from the current one. -/
def styleAttrs : Option MathStyle → Array (String × String)
  | none => #[]
  | some (.display _) => #[("displaystyle", "true"), ("scriptlevel", "0")]
  | some (.text _) => #[("displaystyle", "false"), ("scriptlevel", "0")]
  | some (.script _) => #[("displaystyle", "false"), ("scriptlevel", "1")]
  | some (.scriptscript _) => #[("displaystyle", "false"), ("scriptlevel", "2")]

/-- A generalized fraction's row: its delimiters, sized as the PDF sizes
them — 2.4 em in display style, 1.01 em otherwise — around the `mfrac`. -/
def fracKids (disp : Bool) (spec : FracSpec) (bar : Html.Node) : Array Html.Node :=
  let size := if (spec.style.map (·.rank == 3)).getD disp then "2.4em" else "1.01em"
  let opened : Array Html.Node := match spec.left with
    | some c => #[sizedMo c size]
    | none => #[]
  match spec.right with
  | some c => (opened.push bar).push (sizedMo c size)
  | none => opened.push bar

/-- The script schema around a base: `msub`/`msup`/`msubsup` take children
base, subscript, superscript (MathML Core §3.4.1.1), and a limit-taking
atom in display style takes `munder`/`mover`/`munderover` instead
(§3.4.2.1) — the `lim && display` rule the PDF's `layMathItem` applies.
`.nil` means no script, and a math list emits one element per item, so an
empty child array is exactly an absent script. Scripts wrap in `mrow`,
laid out identically to a lone child (§3.3.1). -/
def scriptNode (limits : Bool) (base : Html.Node)
    (sub sup : Array Html.Node) (subAttrs supAttrs : Array (String × String) := #[]) :
    Html.Node :=
  match sup.isEmpty, sub.isEmpty with
  | true, true => base
  | false, true =>
    .elem (if limits then "mover" else "msup") #[]
      #[base, .elem "mrow" supAttrs sup]
  | true, false =>
    .elem (if limits then "munder" else "msub") #[]
      #[base, .elem "mrow" subAttrs sub]
  | false, false =>
    .elem (if limits then "munderover" else "msubsup") #[]
      #[base, .elem "mrow" subAttrs sub, .elem "mrow" supAttrs sup]

/-- A radical: `msqrt` takes any number of children as an implied row,
`mroot` exactly the base then the index (MathML Core §3.3.3) — the
renderer draws the surd, so no U+221A glyph enters the tree, as none
enters `Math.MList.scalarsList`. -/
def radNode (body deg : Array Html.Node) (degAttrs : Array (String × String) := #[]) :
    Html.Node :=
  match deg.isEmpty with
  | true => .elem "msqrt" #[] body
  | false =>
    .elem "mroot" #[]
      #[.elem "mrow" #[] body, .elem "mrow" degAttrs deg]

/-- The accent schema over an already emitted base. U+0305 uses the
overline operator; every other accent keeps its own scalar. -/
def accentNode (mark : Char) (stretch : Bool) (body : Array Html.Node) : Html.Node :=
  let base := Html.Node.elem "mrow" #[] body
  match mark == '\u0305' with
  | true =>
    .elem "mover" #[("accent", "false")]
      #[base, .elem "mo" #[("stretchy", "true")] #[.text (charText overlineChar)]]
  | false =>
    .elem "mover" #[("accent", "true")]
      #[base, .elem "mo" #[("stretchy", if stretch then "true" else "false")]
        #[.text (charText mark)]]

/-- What a formula's cancel marks read beyond the AST, in thousandths of an
em: the math face's overbar rule and clearance when the page ships its
faces — the two quantities the PDF lays the marks with — else TeX's own
stand-ins, plain TeX's default rule (0.4 pt at the 10 pt base, 40 per
mille) and rule 9's clearance of three rules. -/
structure Marks where
  rule : Nat := 40
  gap : Nat := 120
  /-- Resolved font units for physical math lengths, through the same native
  run resolver as the attachment measurement. -/
  em : MathStyle → Option Int := fun _ => none
  /-- The current style's em and the exact measured input, in the same
  coordinate units. A missing measurement keeps the semantic fallback. -/
  metric : MathStyle → CancelSpec → MList → MList → Option CancelMetric :=
    fun _ _ _ _ => none
  style : MathStyle := .text false
  /-- Font MATH percentages; the unmeasured default is plain TeX's 7/5 pt
  script sizes at its 10 pt base. -/
  scales : ScriptScales := { script := 70, scriptscript := 50 }
  deriving Inhabited

/-- A length in thousandths of an em, as CSS reads it. -/
def milliEm (m : Nat) : String :=
  let fs := toString (m % 1000)
  s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "em"

/-- An explicit transition between the same styles the native walk reads.
The relative font size performs the size change exactly once; `+0` removes
MathML's implicit script step. Descendant transitions go through this same
resolver, including TeX's scriptscript floor. Do not also set CSS math-depth:
Firefox applies its automatic scaling and minimum size on top of these
resolved sizes (the rendered script-size matrix holds this boundary). -/
def relativeStyle (mk : Marks) (st : MathStyle) : Array (String × String) :=
  #[("scriptlevel", "+0"), ("displaystyle", if st.rank == 3 then "true" else "false"),
    ("style", s!"font-size: {measuredEm (sizeFor mk.scales 100 st)
      (sizeFor mk.scales 100 mk.style)}")]

/-- The fraction schema owns its parent and child style transitions.
The IR's absolute style is expressed relative to its enclosing browser style,
so the browser cannot shrink a declared script style a second time. -/
def fracNode (mk : Marks) (disp : Bool) (spec : FracSpec)
    (num den : Array Html.Node) : Html.Node :=
  let st := spec.style.getD mk.style
  let fm := { mk with style := st }
  let bar := Html.Node.elem "mfrac" (ruleAttrs spec.rule (mk.em st))
    #[.elem "mrow" (relativeStyle fm st.fracNum) num,
      .elem "mrow" (relativeStyle fm st.fracDen) den]
  if spec.style.isNone && spec.left.isNone && spec.right.isNone then bar
  else .elem "mrow" (if spec.style.isSome then relativeStyle mk st else #[])
    (fracKids disp spec bar)

/-- A colour as CSS reads it on a MathML element: the palette's custom
property with the literal as its fallback when the colour came from a
named entry — the text runs' emission, so a host page restyles a formula's
colours as it restyles its text's. -/
def inkCss (c : Ir.Color) : Option String → String
  | some n => s!"var(--{n}, {c.css})"
  | none => c.css

/-- A colour switch's reach: the colour every element after the switch in
its list carries, merged into a style the element already declares. Each
element carries it rather than a wrapper around them, because a wrapper
`mrow` would change how MathML infers an operator's form — the `+` after a
switch would become a prefix operator. -/
def paint (ink : Option String) : Html.Node → Html.Node
  | .elem t attrs kids =>
    match ink with
    | none => .elem t attrs kids
    | some css =>
      match attrs.findIdx? (·.1 == "style") with
      | some i => .elem t (attrs.modify i fun (k, v) => (k, s!"color: {css}; " ++ v)) kids
      | none => .elem t (attrs.push ("style", s!"color: {css}")) kids
  | .text s => .text s
  | .style s => .style s
  | .script src nonce => .script src nonce

/-- A cancel mark's diagonal band as a CSS gradient over the padded box: a
corner keyword angles the gradient across the box, so its midline is the
box's other diagonal whatever the box's proportions — `top left` draws the
rising diagonal, `top right` the falling one — and the band is `half` each
side of it, cut by the box's own edges exactly as the PDF's band is. -/
def cancelBand (corner ink half : String) : String :=
  s!"linear-gradient(to {corner}, transparent calc(50% - {half}), {ink} calc(50% - {half}), \
{ink} calc(50% + {half}), transparent calc(50% + {half}))"

/-- Readable, explicitly unmeasured cancellation when no font measurement
is available. CSS strikes and a superscript preserve the semantic content;
they make no claim about measured ink, ray alignment or reserved reach.
The measured path below replaces both the corner head and superscript
placement when the provider supplies an actual math em and input. -/
def cancelNode (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (struck vals : Array Html.Node) (shown : Bool) : Html.Node :=
  let ink := match spec.color with
    | some (c, n) => inkCss c n
    | none => "currentColor"
  let r := mk.rule * (if spec.thick then 2 else 1)
  let half := milliEm ((r + 1) / 2)
  let bands := match mark with
    | .up | .to => cancelBand "top left" ink half
    | .down => cancelBand "top right" ink half
    | .cross => cancelBand "top left" ink half ++ ", " ++ cancelBand "top right" ink half
  let print := "print-color-adjust: exact; -webkit-print-color-adjust: exact"
  let give := if spec.room then "" else
    s!"margin-left: -{milliEm mk.gap}; margin-right: -{milliEm mk.gap}; "
  let box := s!"{give}padding: {milliEm mk.gap}; background-image: {bands}; {print}"
  let head := Html.Node.elem "mspace" #[("style", s!"position: absolute; right: 0; top: 0; \
width: min({milliEm (4 * r)}, 100%); height: min({milliEm (4 * r)}, 100%); background: {ink}; \
clip-path: polygon(0 50%, 100% 0, 50% 100%); {print}")] #[]
  let base := if mark == .to then
      Html.Node.elem "mrow" #[("style", "position: relative; " ++ box)] (struck.push head)
    else Html.Node.elem "mrow" #[("style", box)] struck
  let level : Array (String × String) := match spec.size, disp with
    | .same, _ => #[("scriptlevel", "+0"), ("displaystyle", if disp then "true" else "false")]
    | .step, true => #[("scriptlevel", "+0")]
    | _, _ => #[]
  let tint := match spec.color with
    | some _ => s!"; color: {ink}"
    | none => ""
  let valueRow := Html.Node.elem "mrow"
    (level.push ("style", s!"padding-left: {milliEm mk.gap}" ++ tint)) vals
  -- The direct script child owns the size step; an inner +0 only
  -- preserves the size its mpadded parent already received.
  let valueNode := if spec.room then valueRow else
    .elem "mpadded" (level.push ("width", "0")) #[valueRow]
  if mark == .to || shown then
    .elem "msup" #[("data-cancel-metric", "unmeasured")] #[base, valueNode]
  else
    match base with
    | .elem t attrs kids => .elem t (attrs.push ("data-cancel-metric", "unmeasured")) kids
    | .text s => .text s
    | .style css => .style css
    | .script attrs js => .script attrs js

/-- Baseline-inclusive reach of the measured body, target ink and advance,
and every painted polygon vertex. Only the final common x translation
reserves left overhang; overlap mode keeps the body's advance. -/
private structure CancelReach where
  left : Int
  right : Int
  top : Int
  bot : Int

private def CancelReach.point (r : CancelReach) (p : Int × Int) : CancelReach :=
  { left := min r.left p.1, right := max r.right p.1
    top := max r.top p.2, bot := min r.bot p.2 }

private def cancelReach (metric : CancelMetric) (g : CancelGeom) (shown : Bool) : CancelReach :=
  let i := metric.input
  let body : CancelReach := {
    left := g.shift + min metric.bodyLeft (min 0 i.w)
    right := g.shift + max metric.bodyRight (max 0 i.w)
    top := max 0 i.top, bot := min 0 i.bot }
  let body := if shown then
      ((body.point (g.valueX + i.vleft, g.valueY + i.vbot)).point
        (g.valueX + i.vright, g.valueY + i.vtop)).point
        (g.valueX, g.valueY) |>.point (g.valueX + i.vw, g.valueY)
    else body
  g.polys.foldl (fun r ps => ps.foldl CancelReach.point r) body

/-- One source polygon, with the common room translation and SVG's y-axis
reversal. All coordinates remain integers in the provider's original unit. -/
def cancelPolygon (ink : String) (pad : Int) (ps : Array (Int × Int)) : Html.Node :=
  let points := String.intercalate " " (ps.toList.map fun (x, y) => s!"{x + pad},{-y}")
  .elem "polygon" #[("points", points), ("fill", ink)] #[]

/-- A zero-size placement box uses offsets in the parent's current-style
em, outside any font-size change applied to the visible native child. -/
def cancelAt (em x y : Int) (child : Html.Node) : Html.Node :=
  .elem "mpadded" #[("width", "0"), ("height", "0"), ("depth", "0"),
    ("lspace", measuredEm x em), ("voffset", measuredEm y em)] #[child]

/-- Artifact placement: one SVG user unit is one measured input unit. The
viewport contains the whole measured reach, with its bottom on an explicit
MathML baseline. Its mtext owns the horizontal displacement: browsers clamp
negative mpadded lspace and disagree on absolutely positioned SVG bearings.
At least one em in each dimension keeps zero-advance content nondegenerate.
Body and value remain selectable MathML. -/
def measuredCancelNode (mk : Marks) (metric : CancelMetric) (mark : CancelMark)
    (spec : CancelSpec) (struck vals : Array Html.Node) (shown : Bool) : Html.Node :=
  let em := metric.em
  let i := metric.input
  let g := Math.cancelGeom mark spec.room i
  let visible := mark == .to || shown
  let reach := cancelReach metric g visible
  let (pad, width) := if spec.room then inkRoom reach.left reach.right g.advance
    else (0, max 0 g.advance)
  let ink := match spec.color with
    | some (c, n) => inkCss c n
    | none => "currentColor"
  let sw := max em (reach.right - reach.left)
  let sh := max em (reach.top - reach.bot)
  let sx := reach.left + pad
  let y0 := -reach.bot - sh
  let svg := Html.Node.elem "svg"
    #[("xmlns", "http://www.w3.org/2000/svg"),
      ("viewBox", s!"{sx} {y0} {sw} {sh}"), ("preserveAspectRatio", "none"),
      ("aria-hidden", "true"), ("focusable", "false"),
      ("style", s!"width: {measuredEm sw em}; height: {measuredEm sh em}; \
vertical-align: baseline; overflow: visible; pointer-events: none")]
    (g.polys.map (cancelPolygon ink pad))
  let body := cancelAt em (g.shift + pad) 0 (.elem "mrow" #[] struck)
  let value := cancelAt em (g.valueX + pad) g.valueY
    (paint (spec.color.map fun (c, n) => inkCss c n)
      (.elem "mstyle" (relativeStyle mk (spec.size.style mk.style)) vals))
  let kids := if visible then #[body, value] else #[body]
  .elem "mpadded" #[("width", measuredEm width em),
    ("height", measuredEm reach.top em), ("depth", measuredEm (-reach.bot) em),
    ("data-cancel-metric", "measured")]
    (kids.push (cancelAt em 0 reach.bot
      (.elem "mtext" #[("style", s!"margin-left: {measuredEm sx em}")] #[svg])))

/-- The font provider is the sole source of measured bounds. A nonpositive
em cannot define a CSS projection and takes the named semantic fallback. -/
def cancelWithMetric (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (body value : MList) (struck vals : Array Html.Node) (shown : Bool) : Html.Node :=
  match mk.metric mk.style spec body value with
  | some metric =>
    if 0 < metric.em then measuredCancelNode mk metric mark spec struck vals shown
    else cancelNode mk disp mark spec struck vals shown
  | none => cancelNode mk disp mark spec struck vals shown

mutual

/-- The MathML children of a math list, one element per item, onto `acc`;
`ink` the colour a switch earlier in the list put in force. -/
def listNodes (mk : Marks) (disp : Bool) (ink : Option String) (acc : Array Html.Node) :
    MList → Array Html.Node
  | .nil => acc
  | .cons (.ink c n) rest => listNodes mk disp (some (inkCss c n)) acc rest
  | .cons (.space mu) rest =>
    listNodes mk disp ink (acc.push (paint ink (itemNode mk disp (.space mu)))) rest
  | .cons (.atom cls nuc sup sub lim) rest =>
    listNodes mk disp ink (acc.push (paint ink (itemNode mk disp (.atom cls nuc sup sub lim))))
      rest

/-- One item as one element: an explicit space is `mspace`; an atom is its
nucleus under its script schema (`scriptNode`). `disp` goes false inside
scripts, as the script styles are never display. A colour switch is read
by its list (`listNodes`) and emits nothing of its own. -/
def itemNode (mk : Marks) (disp : Bool) : MItem → Html.Node
  | .space mu =>
    .elem "mspace" (if mu < 0 then
      #[("width", "0"), ("style", s!"margin-inline-end: {muWidth mu}")]
      else #[("width", muWidth mu)]) #[]
  | .ink _ _ => .elem "mrow" #[] #[]
  | .atom cls nuc sup sub lim =>
    scriptNode (lim && disp) (nucNode mk disp cls nuc)
      (listNodes { mk with style := mk.style.sub } false none #[] sub)
      (listNodes { mk with style := mk.style.sup } false none #[] sup)
      (relativeStyle mk mk.style.sub) (relativeStyle mk mk.style.sup)

/-- One nucleus as one element. A lone scalar is final — elaboration
already remapped variables into the Mathematical Alphanumeric block — so a
single-char `mi` carries `mathvariant="normal"`, the one value MathML Core
keeps (§3.2.2), cancelling the renderer's `math-auto` italic: the page
shows exactly the engine's code point, as the PDF does. A word (`\sin`,
`\text`) is a multi-char `mi`, upright because `math-auto` maps single
characters only (§4.2). `mfrac` takes exactly two children (§3.3.2); an
accent is `mover accent="true"` — the mark keeps its size (§3.4.4) and
stretches through the face's variants exactly when the PDF's does — with
the U+0305 overline as `mover accent="false"` over the stretchy U+203E
operator (`overlineChar`). A grid is `mtable`/`mtr`/`mtd`; the table sets
`math-style: compact` on its content (§3.5.1), so a display alignment
restores `displaystyle="true"` (§2.1.6) — amsmath sets align cells in
display style — while an `array` keeps text style, as the PDF's cell
style rule does. -/
def nucNode (mk : Marks) (disp : Bool) (cls : MathClass) : MNucleus → Html.Node
  | .sym c =>
    -- A lone scalar never grows: TeX stretches a delimiter only under
    -- `\left`/`\right` (`delimMo`), and MathML Core's dictionary makes every
    -- fence stretchy, so an `mo` from here declares it cannot.
    let tag := leafTag cls c
    .elem tag (if tag == "mi" then #[("mathvariant", "normal")]
        else if tag == "mo" then #[("stretchy", "false")] else #[])
      #[.text (charText c)]
  | .styled style c =>
    -- A resolved text-sourced alphabet scalar: the plain base letter whose
    -- family/weight/shape ride on real CSS (`style.css`), the same axes the
    -- PDF reads from the one typed style — Chromium honours no non-`normal`
    -- `mathvariant` (MathML Core §3.2.2), so attributes alone would leave
    -- `\mathsf`/`\mathbf` in the default serif. `mathvariant="normal"` goes
    -- on a single-char `mi` only, to cancel the renderer's `math-auto`
    -- italic so the literal base letter stands and CSS decides its shape; a
    -- digit `mn` and an operator `mo` are upright already and need no cancel.
    let tag := leafTag cls c
    let base : Array (String × String) := match tag with
      | "mi" => #[("mathvariant", "normal")]
      | "mo" => #[("stretchy", "false")]
      | _ => #[]
    .elem tag (base.push ("style", style.css)) #[.text (charText c)]
  | .word s => .elem "mi" #[] #[.text s]
  | .list body => .elem "mrow" #[] (listNodes mk disp none #[] body)
  | .alpha _ _ body =>
    -- The driver resolves alphabets before emission; direct callers owe
    -- that same pass (`resolveMathAlphas_covers`). An unresolved `.alpha`
    -- is a MathML `merror` naming its content, never an ordinary `mrow`.
    -- The body still renders inside, so no content is lost.
    .elem "merror" #[] (listNodes mk disp none #[] body)
  | .frac spec num den =>
    let st := spec.style.getD mk.style
    fracNode mk disp spec
      (listNodes { mk with style := st.fracNum } false none #[] num)
      (listNodes { mk with style := st.fracDen } false none #[] den)
  | .rad deg body =>
    radNode (listNodes { mk with style := mk.style.cramp } disp none #[] body)
      (listNodes { mk with style := .scriptscript mk.style.cramped } false none #[] deg)
      (relativeStyle mk (.scriptscript mk.style.cramped))
  | .delim l r body =>
    let opened := match l with
      | some c => #[delimMo c]
      | none => (#[] : Array Html.Node)
    let withBody := listNodes mk disp none opened body
    let closed := match r with
      | some c => withBody.push (delimMo c)
      | none => withBody
    .elem "mrow" #[] closed
  | .big d step =>
    match d with
    | some c => sizedMo c (bigMoSize step)
    | none => .elem "mrow" #[] #[]
  | .accent mark stretch body =>
    accentNode mark stretch (listNodes { mk with style := mk.style.cramp } disp none #[] body)
  | .grid kind rows =>
    let st := match kind with
      | .array _ _ => if mk.style.rank == 3 then .text mk.style.cramped else mk.style
      | .small => .script false
      | .align | .gather => .display false
    -- `smallmatrix` sets its cells in script style, a thin space each side:
    -- 3 mu of the text size, in the script size's em at a 70% script scale.
    let attrs := relativeStyle mk st
    let attrs := if kind == .small then attrs.map fun (k, v) =>
      (k, if k == "style" then v ++ "; padding-inline: 0.238em" else v)
      else attrs
    .elem "mtable" attrs (rowsNodes { mk with style := st } (st.rank == 3) kind #[] rows)
  | .cancel mark spec value body =>
    let st := spec.size.style mk.style
    cancelWithMetric mk disp mark spec body value (listNodes mk disp none #[] body)
      (listNodes { mk with style := st } (st.rank == 3) none #[] value)
      (value matches .cons _ _)

/-- The `mtd` cells of one row. A cell's alignment is the grid kind's for
its column (`GridKind.colAlign`), declared as CSS `text-align` — MathML
Core's `mtd` computes to `table-cell` with a `text-align: center` default
and no `columnalign` attribute (§3.5.3 and its user-agent stylesheet;
styling beyond it is CSS, §2.1.5) — so only a non-centred column carries
the property. An `align` pair's halves abut at the alignment point
(amsmath's `\align@preamble`, the source `GridKind.gapAfter` cites; the
PDF assembly realizes the same zero), so the pair-inner padding of Core's
default `mtd` rule (0.5ex 0.4em) is zeroed on that side; the default
stays as the stand-in for the other gaps, as `gapAfter`'s 2 em between
pairs is already a stated stand-in. A right column declares the standard
value and its `-webkit-` twin: today's Chromium renders every standard
`text-align` on a math cell flush-left and reads only the prefixed forms
(its own default centring is `-webkit-center`; probed 2026-09-20,
Playwright Chromium), and an unsupported value invalidates only its own
declaration (CSS Syntax 3 §declaration error handling), so each engine
keeps the one it understands — delete the twin when Chromium honours the
standard value. -/
def rowNodes (mk : Marks) (disp : Bool) (kind : GridKind) (k : Nat)
    (acc : Array Html.Node) : MRow → Array Html.Node
  | .nil => acc
  | .cons cell rest =>
    let attrs : Array (String × String) := match kind, kind.colAlign k with
      | .align, .right =>
        #[("style",
          "text-align: right; text-align: -webkit-right; padding-right: 0")]
      | .align, .left => #[("style", "text-align: left; padding-left: 0")]
      | .align, .center => #[]
      | .gather, .center => #[]
      | .gather, .left => #[("style", "text-align: left")]
      | .gather, .right =>
        #[("style", "text-align: right; text-align: -webkit-right")]
      | .array _ s, a =>
        let align := match a with
          | .center => none
          | .left => some "text-align: left"
          | .right => some "text-align: right; text-align: -webkit-right"
        match [align, stretchPad s].filterMap id with
        | [] => #[]
        | parts => #[("style", "; ".intercalate parts)]
      -- `\thickspace` before every column but the first (`GridKind.gapAfter`)
      -- and half of `1.5\ex@` above and below each row, in the script size's
      -- em at a 70% script scale.
      | .small, _ =>
        #[("style", if k == 0 then "padding: 0.107em 0" else "padding: 0.107em 0 0.107em 0.397em")]
    rowNodes mk disp kind (k + 1)
      (acc.push (.elem "mtd" attrs (listNodes mk disp none #[] cell))) rest

/-- The `mtr` rows of a grid. -/
def rowsNodes (mk : Marks) (disp : Bool) (kind : GridKind) (acc : Array Html.Node) :
    MRows → Array Html.Node
  | .nil => acc
  | .cons row rest =>
    rowsNodes mk disp kind
      (acc.push (.elem "mtr" #[] (rowNodes mk disp kind 0 #[] row))) rest

end

/-- One formula as its `math` element: `display="block"` for display math
(the user-agent stylesheet then gives it `math-style: normal` and centres
the content box — MathML Core §2.1.1), absent for inline, which the same
stylesheet treats as `inline`. The backend's own attributes (class,
`data-tex`) ride in `extra`. -/
def formula (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks := {}) : Html.Node :=
  .elem "math"
    ((if display then #[("display", "block")] else #[]) ++ extra)
    (listNodes { mk with style := if display then .display false else .text false }
      display none #[] body)

-- The glyph-text fold: what the emission's token leaves spell, in
-- document order, as a pure fold over the AST — the exposed statement of
-- "the leaf text of the MathML emission" the theorem below holds it to.

/-- A list of scalars onto an accumulator. -/
def pushChars (acc : Array Char) : List Char → Array Char
  | [] => acc
  | c :: rest => pushChars (acc.push c) rest

mutual

/-- The glyph text of a math list, MathML document order: per atom the
nucleus, then the subscript, then the superscript (the script elements'
child order — where the PDF census `MList.scalarsList` walks superscript
first); a radical's body before its degree (`mroot` child order); a
delimiter pair around its body; an accent mark after its base, the U+0305
overline as `overlineChar`. Spaces carry no text. -/
def listChars (acc : Array Char) : MList → Array Char
  | .nil => acc
  | .cons x rest => listChars (itemChars acc x) rest

def itemChars (acc : Array Char) : MItem → Array Char
  | .space _ => acc
  | .ink _ _ => acc
  | .atom _ nuc sup sub _ =>
    listChars (listChars (nucChars acc nuc) sub) sup

def nucChars (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .styled _ c => acc.push c
  | .word s => pushChars acc s.toList
  | .list body => listChars acc body
  | .alpha _ _ body => listChars acc body
  | .frac spec num den =>
    let opened := match spec.left with
      | some c => acc.push c
      | none => acc
    let withBody := listChars (listChars opened num) den
    match spec.right with
    | some c => withBody.push c
    | none => withBody
  | .rad deg body => listChars (listChars acc body) deg
  | .delim l r body =>
    let opened := match l with
      | some c => acc.push c
      | none => acc
    let withBody := listChars opened body
    match r with
    | some c => withBody.push c
    | none => withBody
  | .big d _ =>
    match d with
    | some c => acc.push c
    | none => acc
  | .accent mark _ body =>
    (listChars acc body).push
      (match mark == '\u0305' with
        | true => overlineChar
        | false => mark)
  | .grid _ rows => rowsChars acc rows
  -- The struck row, then the value: `msup`'s child order.
  | .cancel _ _ value body => listChars (listChars acc body) value

def rowChars (acc : Array Char) : MRow → Array Char
  | .nil => acc
  | .cons cell rest => rowChars (listChars acc cell) rest

def rowsChars (acc : Array Char) : MRows → Array Char
  | .nil => acc
  | .cons row rest => rowsChars (rowChars acc row) rest

end

mutual

/-- The text content of an emitted node: every `.text` leaf in order. The
emission above puts text only inside `mi`/`mn`/`mo` token leaves, so this
is exactly their leaf text. -/
def nodeChars (acc : Array Char) : Html.Node → Array Char
  | .text s => pushChars acc s.toList
  | .elem _ _ kids => nodeListChars acc kids.toList
  | .style _ => acc
  | .script _ _ => acc

def nodeListChars (acc : Array Char) : List Html.Node → Array Char
  | [] => acc
  | n :: rest => nodeListChars (nodeChars acc n) rest

end

theorem nodeListChars_append (c : Array Char) (l1 l2 : List Html.Node) :
    nodeListChars c (l1 ++ l2) = nodeListChars (nodeListChars c l1) l2 := by
  induction l1 generalizing c with
  | nil => rfl
  | cons n rest ih => simp only [List.cons_append, nodeListChars, ih]

theorem charText_toList (c : Char) : (charText c).toList = [c] :=
  String.toList_ofList

/-- A token leaf's text content is its one scalar. -/
theorem pushChars_charText (acc : Array Char) (c : Char) :
    pushChars acc (charText c).toList = acc.push c := by
  rw [charText_toList]
  rfl

/-- An operator (or any token) element around one scalar contributes
exactly that scalar. -/
theorem moLeaf_chars (t : String) (attrs : Array (String × String))
    (m : Char) (c : Array Char) :
    nodeChars c (.elem t attrs #[.text (charText m)]) = c.push m := by
  show pushChars c (charText m).toList = c.push m
  exact pushChars_charText c m

/-- A delimiter element contributes exactly its scalar. -/
theorem delimMo_chars (m : Char) (c : Array Char) :
    nodeChars c (delimMo m) = c.push m :=
  moLeaf_chars "mo" _ m c

theorem toList_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = true) :
    a.toList = [] := by
  have hs : a.size = 0 := by simpa [Array.isEmpty] using h
  have := a.length_toList
  rw [hs] at this
  exact List.eq_nil_of_length_eq_zero this

/-- A cancel mark's text is its struck row's, then its value's when the
value shows: the head and the marks are an empty element and CSS. -/
theorem cancelNode_chars (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (struck vals : Array Html.Node) (shown : Bool) (c : Array Char) :
    nodeChars c (cancelNode mk disp mark spec struck vals shown)
      = if mark == .to || shown then nodeListChars (nodeListChars c struck.toList) vals.toList
        else nodeListChars c struck.toList := by
  unfold cancelNode
  cases hm : mark == .to <;> cases shown <;> cases spec.room <;>
    simp [nodeChars, nodeListChars, Array.toList_push, nodeListChars_append]

/-- Painting a colour onto an element changes its attributes, never its
text. -/
theorem paint_chars (ink : Option String) (n : Html.Node) (c : Array Char) :
    nodeChars c (paint ink n) = nodeChars c n := by
  cases n with
  | elem t attrs kids =>
    cases ink with
    | none => rfl
    | some css =>
      simp only [paint]
      split <;> rfl
  | text s => rfl
  | style s => rfl
  | script a j => rfl

/-- SVG polygons carry only attributes, regardless of their measured
points. Their census is empty; hiding them never hides native MathML. -/
theorem cancelPolygons_chars (ink : String) (pad : Int)
    (ps : List (Array (Int × Int))) (c : Array Char) :
    nodeListChars c (ps.map (cancelPolygon ink pad)) = c := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [cancelPolygon, nodeChars, nodeListChars] using ih

/-- The measured artifact's text is the native body followed by its target.
Placement offsets, dimensions and SVG never enter the text census. -/
theorem measuredCancelNode_chars (mk : Marks) (metric : CancelMetric)
    (mark : CancelMark) (spec : CancelSpec) (struck vals : Array Html.Node)
    (shown : Bool) (c : Array Char) :
    nodeChars c (measuredCancelNode mk metric mark spec struck vals shown) =
      if mark == .to || shown then nodeListChars (nodeListChars c struck.toList) vals.toList
      else nodeListChars c struck.toList := by
  cases hm : mark == .to <;> cases shown <;> cases spec.room <;>
    simp [measuredCancelNode, hm, cancelAt, nodeChars, nodeListChars,
      Array.toList_map, paint_chars, cancelPolygons_chars]

/-- Either provider result preserves exactly the same native glyph census;
this quantifies over arbitrary metric callbacks, including missing inputs. -/
theorem cancelWithMetric_chars (mk : Marks) (disp : Bool) (mark : CancelMark)
    (spec : CancelSpec) (body value : MList) (struck vals : Array Html.Node)
    (shown : Bool) (c : Array Char) :
    nodeChars c (cancelWithMetric mk disp mark spec body value struck vals shown) =
      if mark == .to || shown then nodeListChars (nodeListChars c struck.toList) vals.toList
      else nodeListChars c struck.toList := by
  unfold cancelWithMetric
  split
  · split <;> first | exact measuredCancelNode_chars .. | exact cancelNode_chars ..
  · exact cancelNode_chars ..

/-- An emitted list grows the accumulator: one element per atom or space,
none removed — the fact that lets `scriptNode` and `radNode` read `.nil`
(no script, no degree) off an empty child array. -/
theorem listNodes_size (mk : Marks) (disp : Bool) :
    ∀ (ink : Option String) (ml : MList) (acc : Array Html.Node),
      acc.size ≤ (listNodes mk disp ink acc ml).size
  | _, .nil, _ => Nat.le_refl _
  | _, .cons (.ink co n) rest, acc => listNodes_size mk disp _ rest acc
  | ink, .cons (.space mu) rest, acc =>
    Nat.le_trans (by simp)
      (listNodes_size mk disp ink rest (acc.push (paint ink (itemNode mk disp (.space mu)))))
  | ink, .cons (.atom cls nuc sup sub lim) rest, acc =>
    Nat.le_trans (by simp)
      (listNodes_size mk disp ink rest
        (acc.push (paint ink (itemNode mk disp (.atom cls nuc sup sub lim)))))

/-- An empty emission is an empty list, on the fold: the glyph text of a
list whose emission is empty is the accumulator unchanged. -/
theorem listChars_of_empty (mk : Marks) (disp : Bool) :
    ∀ (ink : Option String) (ml : MList),
      (listNodes mk disp ink #[] ml).isEmpty = true → ∀ (c : Array Char), listChars c ml = c
  | _, .nil, _, _ => rfl
  | _, .cons (.ink co n) rest, h, c => listChars_of_empty mk disp _ rest h c
  | ink, .cons (.space mu) rest, h, c => by
    exfalso
    have hs := listNodes_size mk disp ink rest #[paint ink (itemNode mk disp (.space mu))]
    have h0 : (listNodes mk disp ink #[paint ink (itemNode mk disp (.space mu))] rest).size
        = 0 := by
      simpa [listNodes, Array.isEmpty_iff_size_eq_zero] using h
    have h1 : (#[paint ink (itemNode mk disp (.space mu))] : Array Html.Node).size = 1 := rfl
    omega
  | ink, .cons (.atom cls nuc sup sub lim) rest, h, c => by
    exfalso
    have hs := listNodes_size mk disp ink rest
      #[paint ink (itemNode mk disp (.atom cls nuc sup sub lim))]
    have h0 : (listNodes mk disp ink
        #[paint ink (itemNode mk disp (.atom cls nuc sup sub lim))] rest).size = 0 := by
      simpa [listNodes, Array.isEmpty_iff_size_eq_zero] using h
    have h1 : (#[paint ink (itemNode mk disp (.atom cls nuc sup sub lim))] :
        Array Html.Node).size = 1 := rfl
    omega

/-- The script schema's text is base, subscript, superscript, whether the
scripts ride beside (`msub` family) or above and below (`munder` family):
the two schemas share their child order. -/
theorem scriptNode_chars (limits : Bool) (base : Html.Node)
    (sub sup : Array Html.Node) (subAttrs supAttrs : Array (String × String)) (c : Array Char) :
    nodeChars c (scriptNode limits base sub sup subAttrs supAttrs)
      = nodeListChars (nodeListChars (nodeChars c base) sub.toList)
          sup.toList := by
  unfold scriptNode
  cases hsup : sup.isEmpty <;> cases hsub : sub.isEmpty
  · show nodeListChars c [base, .elem "mrow" subAttrs sub, .elem "mrow" supAttrs sup]
        = _
    rfl
  · rw [toList_of_isEmpty hsub]
    show nodeListChars c [base, .elem "mrow" supAttrs sup] = _
    rfl
  · rw [toList_of_isEmpty hsup]
    show nodeListChars c [base, .elem "mrow" subAttrs sub] = _
    rfl
  · rw [toList_of_isEmpty hsub, toList_of_isEmpty hsup]
    rfl

/-- A radical's text is its body then its degree, `msqrt` and `mroot`
alike. -/
theorem radNode_chars (body deg : Array Html.Node) (degAttrs : Array (String × String))
    (c : Array Char) :
    nodeChars c (radNode body deg degAttrs)
      = nodeListChars (nodeListChars c body.toList) deg.toList := by
  unfold radNode
  cases hdeg : deg.isEmpty
  · show nodeListChars c [.elem "mrow" #[] body, .elem "mrow" degAttrs deg] = _
    rfl
  · rw [toList_of_isEmpty hdeg]
    rfl

/-- Fraction delimiters enclose numerator then denominator in the native
text order; the child styles and rule never contribute text. -/
theorem fracNode_chars (mk : Marks) (disp : Bool) (spec : FracSpec)
    (num den : Array Html.Node) (c : Array Char) :
    nodeChars c (fracNode mk disp spec num den) =
      let opened := match spec.left with | some ch => c.push ch | none => c
      let withBar := nodeListChars (nodeListChars opened num.toList) den.toList
      match spec.right with | some ch => withBar.push ch | none => withBar := by
  rcases spec with ⟨l, r, rule, style⟩
  cases l <;> cases r <;> cases style <;>
    simp [fracNode, fracKids, nodeChars, nodeListChars, sizedMo, pushChars_charText]

/-- An accent emits its base followed by the declared accent scalar. -/
theorem accentNode_chars (mark : Char) (stretch : Bool) (body : Array Html.Node)
    (c : Array Char) :
    nodeChars c (accentNode mark stretch body) =
      (nodeListChars c body.toList).push
        (match mark == '\u0305' with | true => overlineChar | false => mark) := by
  cases h : mark == '\u0305' <;>
    simp [accentNode, h, nodeChars, nodeListChars, pushChars_charText]

mutual

theorem listNodes_chars (mk : Marks) (disp : Bool) :
    ∀ (ink : Option String) (ml : MList) (acc : Array Html.Node) (c : Array Char),
      nodeListChars c (listNodes mk disp ink acc ml).toList
        = listChars (nodeListChars c acc.toList) ml
  | _, .nil, acc, c => rfl
  | _, .cons (.ink co n) rest, acc, c => by
    show nodeListChars c (listNodes mk disp (some (inkCss co n)) acc rest).toList
        = listChars (nodeListChars c acc.toList) rest
    exact listNodes_chars mk disp _ rest acc c
  | ink, .cons (.space mu) rest, acc, c => by
    show nodeListChars c (listNodes mk disp ink
        (acc.push (paint ink (itemNode mk disp (.space mu)))) rest).toList
      = listChars (itemChars (nodeListChars c acc.toList) (.space mu)) rest
    rw [listNodes_chars mk disp ink rest, Array.toList_push, nodeListChars_append]
    simp only [nodeListChars]
    rw [paint_chars, itemNode_chars mk disp]
  | ink, .cons (.atom cls nuc sup sub lim) rest, acc, c => by
    show nodeListChars c (listNodes mk disp ink
        (acc.push (paint ink (itemNode mk disp (.atom cls nuc sup sub lim)))) rest).toList
      = listChars (itemChars (nodeListChars c acc.toList) (.atom cls nuc sup sub lim)) rest
    rw [listNodes_chars mk disp ink rest, Array.toList_push, nodeListChars_append]
    simp only [nodeListChars]
    rw [paint_chars, itemNode_chars mk disp]

theorem itemNode_chars (mk : Marks) (disp : Bool) :
    ∀ (x : MItem) (c : Array Char),
      nodeChars c (itemNode mk disp x) = itemChars c x
  | .space _, c => rfl
  | .ink _ _, c => rfl
  | .atom cls nuc sup sub lim, c => by
    show nodeChars c (scriptNode (lim && disp) (nucNode mk disp cls nuc)
        (listNodes { mk with style := mk.style.sub } false none #[] sub)
        (listNodes { mk with style := mk.style.sup } false none #[] sup) _ _)
      = listChars (listChars (nucChars c nuc) sub) sup
    rw [scriptNode_chars, nucNode_chars mk disp cls nuc c,
      listNodes_chars _ false none sub #[] (nucChars c nuc),
      listNodes_chars _ false none sup #[]]
    rfl

theorem nucNode_chars (mk : Marks) (disp : Bool) (cls : MathClass) :
    ∀ (nuc : MNucleus) (c : Array Char),
      nodeChars c (nucNode mk disp cls nuc) = nucChars c nuc
  | .sym ch, c => by
    show pushChars c (charText ch).toList = c.push ch
    exact pushChars_charText c ch
  | .styled _ ch, c => by
    show pushChars c (charText ch).toList = c.push ch
    exact pushChars_charText c ch
  | .word _, c => rfl
  | .list body, c => by
    show nodeListChars c (listNodes mk disp none #[] body).toList = listChars c body
    rw [listNodes_chars mk disp none body #[] c]
    rfl
  | .alpha _ _ body, c => by
    show nodeListChars c (listNodes mk disp none #[] body).toList = listChars c body
    rw [listNodes_chars mk disp none body #[] c]
    rfl
  | .frac spec num den, c => by
    show nodeChars c (fracNode mk disp spec
        (listNodes { mk with style := (spec.style.getD mk.style).fracNum } false none #[] num)
        (listNodes { mk with style := (spec.style.getD mk.style).fracDen } false none #[] den))
      = nucChars c (.frac spec num den)
    rw [fracNode_chars]
    dsimp only
    rw [listNodes_chars _ false none num #[], listNodes_chars _ false none den #[]]
    rfl
  | .rad deg body, c => by
    show nodeChars c (radNode (listNodes { mk with style := mk.style.cramp } disp none #[] body)
        (listNodes { mk with style := .scriptscript mk.style.cramped } false none #[] deg) _)
      = listChars (listChars c body) deg
    rw [radNode_chars, listNodes_chars _ disp none body #[] c,
      listNodes_chars _ false none deg #[]]
    rfl
  | .delim l r body, c => by
    cases l with
    | none =>
      cases r with
      | none =>
        show nodeListChars c (listNodes mk disp none #[] body).toList = listChars c body
        rw [listNodes_chars mk disp none body #[] c]
        rfl
      | some cr =>
        show nodeListChars c
            ((listNodes mk disp none #[] body).push (delimMo cr)).toList
          = (listChars c body).push cr
        rw [Array.toList_push, nodeListChars_append,
          listNodes_chars mk disp none body #[] c]
        show nodeChars (listChars c body) (delimMo cr) = _
        rw [delimMo_chars]
    | some cl =>
      cases r with
      | none =>
        show nodeListChars c (listNodes mk disp none #[delimMo cl] body).toList
          = listChars (c.push cl) body
        rw [listNodes_chars mk disp none body]
        show listChars (nodeChars c (delimMo cl)) body = _
        rw [delimMo_chars]
      | some cr =>
        show nodeListChars c
            ((listNodes mk disp none #[delimMo cl] body).push (delimMo cr)).toList
          = (listChars (c.push cl) body).push cr
        rw [Array.toList_push, nodeListChars_append,
          listNodes_chars mk disp none body]
        show nodeChars (listChars (nodeChars c (delimMo cl)) body)
            (delimMo cr) = _
        rw [delimMo_chars, delimMo_chars]
  | .big d step, c => by
    cases d with
    | none => rfl
    | some ch => exact moLeaf_chars "mo" _ ch c
  | .accent mark stretch body, c => by
    show nodeChars c (accentNode mark stretch
        (listNodes { mk with style := mk.style.cramp } disp none #[] body))
      = (listChars c body).push _
    rw [accentNode_chars, listNodes_chars _ disp none body #[] c]
    rfl
  | .grid kind rows, c => by
    show nodeListChars c (rowsNodes _ _ kind #[] rows).toList = rowsChars c rows
    rw [rowsNodes_chars]
    rfl
  | .cancel mark spec value body, c => by
    show nodeChars c (cancelWithMetric mk disp mark spec body value
        (listNodes mk disp none #[] body)
        (listNodes { mk with style := spec.size.style mk.style }
          ((spec.size.style mk.style).rank == 3) none #[] value) (value matches .cons _ _))
      = listChars (listChars c body) value
    have hs := listNodes_chars mk disp none body #[] c
    have hv := listNodes_chars { mk with style := spec.size.style mk.style }
      ((spec.size.style mk.style).rank == 3) none value #[]
    simp only [nodeListChars] at hs hv
    rw [cancelWithMetric_chars, hs, hv]
    cases value with
    | nil => simp [listChars]
    | cons _ _ => simp

theorem rowNodes_chars (mk : Marks) (disp : Bool) (kind : GridKind) :
    ∀ (row : MRow) (k : Nat) (acc : Array Html.Node) (c : Array Char),
      nodeListChars c (rowNodes mk disp kind k acc row).toList
        = rowChars (nodeListChars c acc.toList) row
  | .nil, _, acc, c => rfl
  | .cons cell rest, k, acc, c => by
    show nodeListChars c (rowNodes mk disp kind (k + 1) _ rest).toList
        = rowChars (listChars (nodeListChars c acc.toList) cell) rest
    rw [rowNodes_chars mk disp kind rest, Array.toList_push,
      nodeListChars_append]
    simp only [nodeListChars]
    show rowChars (nodeListChars (nodeListChars c acc.toList)
        (listNodes mk disp none #[] cell).toList) rest = _
    rw [listNodes_chars mk disp none cell #[]]
    rfl

theorem rowsNodes_chars (mk : Marks) (disp : Bool) (kind : GridKind) :
    ∀ (rows : MRows) (acc : Array Html.Node) (c : Array Char),
      nodeListChars c (rowsNodes mk disp kind acc rows).toList
        = rowsChars (nodeListChars c acc.toList) rows
  | .nil, acc, c => rfl
  | .cons row rest, acc, c => by
    show nodeListChars c (rowsNodes mk disp kind _ rest).toList
        = rowsChars (rowChars (nodeListChars c acc.toList) row) rest
    rw [rowsNodes_chars mk disp kind rest, Array.toList_push,
      nodeListChars_append]
    simp only [nodeListChars]
    show rowsChars (nodeListChars (nodeListChars c acc.toList)
        (rowNodes mk disp kind 0 #[] row).toList) rest = _
    rw [rowNodes_chars mk disp kind row 0 #[]]
    rfl

end

/-- The MathML census: the emission's leaf text — the `mi`/`mn`/`mo`
contents in order, which is all the text the element carries — equals the
pure glyph-text fold over the same math list, for either display mode,
whatever backend attributes ride on the element and whatever the marks'
measures are. What this holds fixed: the projection to MathML drops no
glyph the AST carries and invents none beyond it — a colour switch paints,
a cancel mark's strike and arrowhead are decorative SVG polygons (CSS in
the unmeasured fallback), text of neither; the fold's agreement with the PDF's coverage census
(`Math.MList.scalarsList` — same scalars, its order, overline excepted)
is pinned by test in `mathmlChecks`. -/
theorem mathml_glyphs_agree (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) :
    nodeChars #[] (formula display extra body mk) = listChars #[] body := by
  simp only [formula, nodeChars]
  rw [listNodes_chars _ display none body #[] #[]]
  rfl

/-- The HTML projection consumes the same resolved math list the PDF layout
consumes: its typed MathML leaf text is exactly that list's glyph-text
projection, after the one shared alphabet pass. -/
theorem resolveMathAlphas_html_agree (coverage : Math.MathAlphabetCoverage)
    (display : Bool) (extra : Array (String × String)) (body : MList)
    (mk : Marks) :
    nodeChars #[]
      (formula display extra (Math.resolveMathAlphas coverage body) mk) =
      listChars #[] (Math.resolveMathAlphas coverage body) :=
  mathml_glyphs_agree display extra (Math.resolveMathAlphas coverage body) mk

end LeanTex.Core.MathMl
