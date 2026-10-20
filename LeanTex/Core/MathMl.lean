module

public import LeanTex.Core.Html
public import LeanTex.Core.Math

/-! Math on the HTML backend: MathML Core emitted from the math list the PDF lays out, every leaf
through the typed tree's escaper, and no script. -/

namespace LeanTex.Core.MathMl

open LeanTex.Core LeanTex.Core.Math

/-- One scalar as the string a token leaf carries. -/
def charText (c : Char) : String := String.ofList [c]

/-- The overline operator U+0305 renders as: U+203E, stretchy in MathML Core's dictionary. -/
public def overlineChar : Char := '\u203E'

/-- The declaration that sets a math text run as TeX sets a box: its spaces as written, its line
unbroken. -/
public def keepLineCss : String := "white-space: pre"

/-- The token element a lone scalar sets in by its TeX class: `mo`, else `mn` for a digit, else
`mi` (MathML Core §3.2). -/
public def leafTag (cls : MathClass) (c : Char) : String :=
  match cls with
  | .op | .bin | .rel | .opening | .closing | .punct => "mo"
  | .ord | .inner => if c.isDigit then "mn" else "mi"

/-- A measured coordinate over its provider's em, to six decimal places. -/
public def measuredEm (n em : Int) : String :=
  let d := (max 1 em).toNat
  let m := (n.natAbs * 1000000 + d / 2) / d
  let fs := toString (m % 1000000)
  (if n < 0 && m != 0 then "-" else "") ++
    s!"{m / 1000000}." ++ "".pushn '0' (6 - fs.length) ++ fs ++ "em"

/-- An advance as a nonnegative MathML width and a negative CSS end margin. -/
public def widthParts (width : Int) : Int × Int := (max 0 width, min 0 width)

/-- A fact of the artifact: width and end margin preserve every signed advance. -/
public theorem widthParts_contract (width : Int) :
    let p := widthParts width
    0 ≤ p.1 ∧ p.2 ≤ 0 ∧ p.1 + p.2 = width := by
  dsimp [widthParts]
  omega

/-- One advance projection for spacing and measured attachment boxes. -/
def advanceAttrs (em width : Int) : Array (String × String) :=
  let (w, margin) := widthParts width
  if margin < 0 then
    #[("width", "0"), ("style", s!"margin-inline-end: {measuredEm margin em}")]
  else #[("width", measuredEm w em)]

/-- The cell padding that sets a stretched array's rows `\arraystretch` baselines apart: half the
stretch past one, of the PDF's 1.2 em baseline, on MathML Core's 0.5ex; `none` at the default. -/
def stretchPad (stretch : Nat) : Option String :=
  if stretch ≤ 1000 then none else
    let m := (stretch - 1000) * 6 / 10
    let fs := toString (m % 1000)
    let em := s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "em"
    some s!"padding-top: calc(0.5ex + {em}); padding-bottom: calc(0.5ex + {em})"

/-- A `\left`/`\right` delimiter: stretchy and symmetric about the math axis (MathML Core
§3.2.4.2). -/
def delimMo (c : Char) : Html.Node :=
  .elem "mo" #[("stretchy", "true"), ("symmetric", "true")]
    #[.text (charText c)]

/-- A `\genfrac` delimiter stretched to exactly `size`. -/
def sizedMo (c : Char) (size : String) : Html.Node :=
  .elem "mo" #[("stretchy", "true"), ("symmetric", "true"), ("minsize", size),
    ("maxsize", size)] #[.text (charText c)]

/-- The size an amsmath sized delimiter stretches to in em: `Math.bigTarget` for a one-em `(`. -/
def bigMoSize (step : Nat) : String :=
  let t := (Math.bigTarget 1000 1000 step).toNat
  let frac := ((toString (1000 + t % 1000)).drop 1).toString
  s!"{t / 1000}.{frac}em"

/-- A fraction's declared rule as `mfrac`'s `linethickness`, in measured em when known. -/
def ruleAttrs (rule : Option Dim.Length) (em : Option Int) : Array (String × String) :=
  match rule with
  | none => #[]
  | some t =>
    let width := max t 0
    let m := width * (1000 : Int) / Dim.bp 1
    let fs := toString (m % 1000)
    let points := if m == 0 then "0" else s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "pt"
    let length := match em with
      | some size => if 0 < size then measuredEm width.units size else points
      | none => points
    #[("linethickness", length)]

/-- A style switch as MathML Core's `displaystyle` and absolute `scriptlevel` (§2.1.6). -/
public def styleAttrs : Option MathStyle → Array (String × String)
  | none => #[]
  | some (.display _) => #[("displaystyle", "true"), ("scriptlevel", "0")]
  | some (.text _) => #[("displaystyle", "false"), ("scriptlevel", "0")]
  | some (.script _) => #[("displaystyle", "false"), ("scriptlevel", "1")]
  | some (.scriptscript _) => #[("displaystyle", "false"), ("scriptlevel", "2")]

/-- A generalized fraction's row: its delimiters, sized as the PDF sizes them, around the
`mfrac`. -/
def fracKids (disp : Bool) (spec : FracSpec) (bar : Html.Node) : Array Html.Node :=
  let size := if (spec.style.map (·.rank == 3)).getD disp then "2.4em" else "1.01em"
  let opened : Array Html.Node := match spec.left with
    | some c => #[sizedMo c size]
    | none => #[]
  match spec.right with
  | some c => (opened.push bar).push (sizedMo c size)
  | none => opened.push bar

/-- The script schema around a base: `msub`/`msup`/`msubsup`, or `munder`/`mover`/`munderover`
for display limits. -/
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

/-- A radical: `msqrt`, or `mroot` with its index; the renderer draws the surd. -/
def radNode (body deg : Array Html.Node) (degAttrs : Array (String × String) := #[]) :
    Html.Node :=
  match deg.isEmpty with
  | true => .elem "msqrt" #[] body
  | false =>
    .elem "mroot" #[]
      #[.elem "mrow" #[] body, .elem "mrow" degAttrs deg]

/-- The accent schema over an emitted base; U+0305 uses the overline operator. -/
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

/-- What a formula's cancel marks and lengths read beyond the AST, with TeX's stand-ins where no
face is measured. -/
public structure Marks where
  /-- The overbar rule in thousandths of an em; unmeasured, plain TeX's 0.4 pt at 10 pt. -/
  rule : Nat := 40
  /-- The overbar clearance in thousandths of an em; unmeasured, TeX rule 9's three rules. -/
  gap : Nat := 120
  /-- Resolved font units for physical math lengths. -/
  em : MathStyle → Option Int := fun _ => none
  /-- The ambient text size's em, for text-sourced alphabets. -/
  textEm : MathStyle → Option Int := fun _ => none
  /-- The current style's em and measured input; `none` keeps the semantic fallback. -/
  metric : MathStyle → CancelSpec → MList → MList → Option CancelMetric :=
    fun _ _ _ _ => none
  style : MathStyle := .text false
  /-- `\minalignsep` as a CSS length in the page's print unit; `1em` at the 10 pt base. -/
  alignSep : String := "1em"
  /-- Font MATH percentages; unmeasured, plain TeX's 7/5 pt script sizes at 10 pt. -/
  scales : ScriptScales := { script := 70, scriptscript := 50 }
  /-- A colour no palette names, as the page ships it. -/
  literal : Ir.Color → String := Ir.Color.css
  deriving Inhabited

/-- A length in thousandths of an em, as CSS reads it. -/
public def milliEm (m : Nat) : String :=
  let fs := toString (m % 1000)
  s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "em"

/-- An explicit transition between the styles the native walk reads; CSS `math-depth` stays unset,
since Firefox would scale a second time. -/
def relativeStyle (mk : Marks) (st : MathStyle) : Array (String × String) :=
  #[("scriptlevel", "+0"), ("displaystyle", if st.rank == 3 then "true" else "false"),
    ("style", s!"font-size: {measuredEm (sizeFor mk.scales 100 st)
      (sizeFor mk.scales 100 mk.style)}")]

/-- The fraction schema, owning its parent and child style transitions. -/
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

/-- A colour as CSS reads it on a MathML element: the palette's property with a literal fallback,
else the literal. -/
def inkCss (lit : Ir.Color → String) (c : Ir.Color) : Option Ir.ColorRef → String
  | some n => s!"var({n.property}, {c.css})"
  | none => lit c

/-- A colour switch's colour merged into an element's style; a wrapping `mrow` would change
operator forms. -/
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

/-- A cancel mark's diagonal band as a CSS gradient over the padded box. -/
def cancelBand (corner ink half : String) : String :=
  s!"linear-gradient(to {corner}, transparent calc(50% - {half}), {ink} calc(50% - {half}), \
{ink} calc(50% + {half}), transparent calc(50% + {half}))"

/-- Unmeasured cancellation: CSS strikes and a superscript, for a formula without font metrics. -/
def cancelNode (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (struck vals : Array Html.Node) (shown : Bool) : Html.Node :=
  let ink := match spec.color with
    | some (c, n) => inkCss mk.literal c n
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
  -- The direct script child owns the size step.
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

/-- Baseline-inclusive reach of the measured body, target ink and advance, and every polygon
vertex. -/
private structure CancelReach where
  left : Int
  right : Int
  top : Int
  bot : Int

private def CancelReach.point (r : CancelReach) (p : Int × Int) : CancelReach :=
  { left := min r.left p.1, right := max r.right p.1
    top := max r.top p.2, bot := min r.bot p.2 }

private def cancelReach (metric : CancelMetric) (g : CancelGeom) : CancelReach :=
  let i := metric.input
  let body : CancelReach := {
    left := g.shift + min metric.bodyLeft (min 0 i.w)
    right := g.shift + max metric.bodyRight (max 0 i.w)
    top := max 0 i.top, bot := min 0 i.bot }
  let body := if i.hasValueInk then
      (body.point (g.valueX + i.vleft, g.valueY + i.vbot)).point
        (g.valueX + i.vright, g.valueY + i.vtop)
    else body
  let body := if i.hasValueInk || i.vw != 0 then
      { body with left := min body.left (min g.valueX (g.valueX + i.vw))
                  right := max body.right (max g.valueX (g.valueX + i.vw)) }
    else body
  g.polys.foldl (fun r ps => ps.foldl CancelReach.point r) body

/-- One source polygon with the common room translation and SVG's y-axis reversal. -/
def cancelPolygon (ink : String) (pad : Int) (ps : Array (Int × Int)) : Html.Node :=
  let points := String.intercalate " " (ps.toList.map fun (x, y) => s!"{x + pad},{-y}")
  .elem "polygon" #[("points", points), ("fill", ink)] #[]

/-- A zero-size placement box offset in the parent's em; its margins keep signed offsets. -/
def cancelAt (em x y : Int) (child : Html.Node) : Html.Node :=
  .elem "mpadded" #[("width", "0"), ("height", "0"), ("depth", "0"),
    ("lspace", "0"), ("voffset", measuredEm y em),
    ("style", s!"margin-left: {measuredEm x em}; margin-right: {measuredEm (-x) em}")]
    #[child]

/-- Measured cancellation as an SVG over selectable MathML, one SVG unit per measured unit. -/
def measuredCancelNode (mk : Marks) (metric : CancelMetric) (mark : CancelMark)
    (spec : CancelSpec) (struck vals : Array Html.Node) (shown : Bool) : Html.Node :=
  let em := metric.em
  let i := metric.input
  let g := Math.cancelGeom mark spec.room i
  let visible := mark == .to || shown
  let reach := cancelReach metric g
  let (pad, width) := if spec.room then inkRoom reach.left reach.right g.advance
    else (0, g.advance)
  let ink := match spec.color with
    | some (c, n) => inkCss mk.literal c n
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
    (paint (spec.color.map fun (c, n) => inkCss mk.literal c n)
      (.elem "mstyle" (relativeStyle mk (spec.size.style mk.style)) vals))
  let kids := if visible then #[body, value] else #[body]
  .elem "mpadded" (advanceAttrs em width ++
    #[("height", measuredEm reach.top em), ("depth", measuredEm (-reach.bot) em),
      ("data-cancel-metric", "measured")])
    (kids.push (cancelAt em sx reach.bot (.elem "mtext" #[] #[svg])))

/-- Measured cancellation when the provider gives a positive em, else the unmeasured fallback. -/
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
public def listNodes (mk : Marks) (disp : Bool) (ink : Option String) (acc : Array Html.Node) :
    MList → Array Html.Node
  | .nil => acc
  | .cons (.ink c n) rest => listNodes mk disp (some (inkCss mk.literal c n)) acc rest
  | .cons (.space mu) rest =>
    listNodes mk disp ink (acc.push (paint ink (itemNode mk disp (.space mu)))) rest
  | .cons (.atom cls nuc sup sub lim) rest =>
    listNodes mk disp ink (acc.push (paint ink (itemNode mk disp (.atom cls nuc sup sub lim))))
      rest

/-- One item as one element; a colour switch emits nothing of its own. -/
public def itemNode (mk : Marks) (disp : Bool) : MItem → Html.Node
  | .space mu => -- Signed mu: 18ths of the current em (TeXbook p. 168).
    .elem "mspace" (advanceAttrs 18 mu) #[]
  | .ink _ _ => .elem "mrow" #[] #[]
  | .atom cls nuc sup sub lim =>
    scriptNode (lim && disp) (nucNode mk disp cls nuc)
      (listNodes { mk with style := mk.style.sub } false none #[] sub)
      (listNodes { mk with style := mk.style.sup } false none #[] sup)
      (relativeStyle mk mk.style.sub) (relativeStyle mk mk.style.sup)

/-- One nucleus as one element; a lone scalar is final, so a single-char `mi` cancels `math-auto`
italic with `mathvariant="normal"`. -/
public def nucNode (mk : Marks) (disp : Bool) (cls : MathClass) : MNucleus → Html.Node
  | .sym c =>
    -- A lone scalar never stretches: only `\left`/`\right` grow a delimiter.
    let tag := leafTag cls c
    .elem tag (if tag == "mi" then #[("mathvariant", "normal")]
        else if tag == "mo" then #[("stretchy", "false")] else #[])
      #[.text (charText c)]
  | .styled style c =>
    -- Chromium honours no non-`normal` `mathvariant`, so a text style's axes ride on CSS.
    let tag := leafTag cls c
    let base : Array (String × String) := match tag with
      | "mi" => #[("mathvariant", "normal")]
      | "mo" => #[("stretchy", "false")]
      | _ => #[]
    -- Firefox drops a plain relative font size beside a family change; `calc` keeps the ratio.
    let sizing := match mk.textEm mk.style, mk.em mk.style with
      | some text, some math =>
        if text > 0 && math > 0 then s!"; font-size: calc({measuredEm text math})" else ""
      | _, _ => ""
    .elem tag (base.push ("style", style.css ++ sizing)) #[.text (charText c)]
  -- A word sets upright, so a one-scalar word cancels `math-auto` italic as a lone scalar does.
  | .word s =>
    .elem "mi" ((if s.length == 1 then #[("mathvariant", "normal")] else #[]).push
      ("style", keepLineCss)) #[.text s]
  | .list body => .elem "mrow" #[] (listNodes mk disp none #[] body)
  | .alpha _ _ body =>
    -- An unresolved alphabet is an `merror` around its content.
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
      | .align | .aligned _ | .gather => .display false
    -- `smallmatrix`: script-style cells, a thin space a side: the text's 3 mu in a 70% script em.
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

/-- The `mtd` cells of one row: a non-centred column declares CSS `text-align`, a right one
with its `-webkit-` twin for Chromium. -/
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
      -- `aligned`'s pairs stand `\minalignsep` apart, half on each side.
      | .aligned _, .right =>
        #[("style", "text-align: right; text-align: -webkit-right; padding-right: 0" ++
          (if k == 0 then "" else s!"; padding-left: calc({mk.alignSep} / 2)"))]
      | .aligned t, .left =>
        #[("style", "text-align: left; padding-left: 0" ++
          (if rest matches .nil then (if t then s!"; padding-right: {mk.alignSep}" else "")
           else s!"; padding-right: calc({mk.alignSep} / 2)"))]
      | .aligned _, .center => #[]
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
      -- `\thickspace` before later columns, half `1.5\ex@` above and below, in a 70% script em.
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

/-- One formula's children: its list in the formula's own style. -/
public def formulaKids (display : Bool) (body : MList) (mk : Marks := {}) :
    Array Html.Node :=
  listNodes { mk with style := if display then .display false else .text false }
    display none #[] body

/-- One formula as its `math` element, `display="block"` for display math; `extra` carries the
backend's attributes. -/
public def formula (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks := {}) : Html.Node :=
  .elem "math"
    ((if display then #[("display", "block")] else #[]) ++ extra)
    (formulaKids display body mk)

/-- One formula as a row inside an open `math` element, `displaystyle` standing for `display`. -/
public def formulaRow (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks := {}) : Html.Node :=
  .elem "mrow"
    ((if display then #[("displaystyle", "true")] else #[]) ++ extra)
    (formulaKids display body mk)

/-- A list of scalars onto an accumulator. -/
def pushChars (acc : Array Char) : List Char → Array Char
  | [] => acc
  | c :: rest => pushChars (acc.push c) rest

mutual

/-- The glyph text of a math list in MathML document order; spaces carry none. -/
public def listChars (acc : Array Char) : MList → Array Char
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
  | .cancel _ _ value body => listChars (listChars acc body) value

def rowChars (acc : Array Char) : MRow → Array Char
  | .nil => acc
  | .cons cell rest => rowChars (listChars acc cell) rest

def rowsChars (acc : Array Char) : MRows → Array Char
  | .nil => acc
  | .cons row rest => rowsChars (rowChars acc row) rest

end

mutual

/-- The text content of an emitted node: every `.text` leaf in order. -/
public def nodeChars (acc : Array Char) : Html.Node → Array Char
  | .text s => pushChars acc s.toList
  | .elem _ _ kids => nodeListChars acc kids.toList
  | .style _ => acc
  | .script _ _ => acc

public def nodeListChars (acc : Array Char) : List Html.Node → Array Char
  | [] => acc
  | n :: rest => nodeListChars (nodeChars acc n) rest

end

public theorem nodeListChars_nil (acc : Array Char) : nodeListChars acc [] = acc := by
  simp only [nodeListChars]

public theorem nodeListChars_cons (acc : Array Char) (n : Html.Node) (rest : List Html.Node) :
    nodeListChars acc (n :: rest) = nodeListChars (nodeChars acc n) rest := by
  simp only [nodeListChars]

theorem nodeListChars_append (c : Array Char) (l1 l2 : List Html.Node) :
    nodeListChars c (l1 ++ l2) = nodeListChars (nodeListChars c l1) l2 := by
  induction l1 generalizing c with
  | nil => rfl
  | cons n rest ih => simp only [List.cons_append, nodeListChars, ih]

theorem charText_toList (c : Char) : (charText c).toList = [c] :=
  String.toList_ofList

theorem pushChars_charText (acc : Array Char) (c : Char) :
    pushChars acc (charText c).toList = acc.push c := by
  rw [charText_toList]
  rfl

theorem moLeaf_chars (t : String) (attrs : Array (String × String))
    (m : Char) (c : Array Char) :
    nodeChars c (.elem t attrs #[.text (charText m)]) = c.push m := by
  show pushChars c (charText m).toList = c.push m
  exact pushChars_charText c m

theorem delimMo_chars (m : Char) (c : Array Char) :
    nodeChars c (delimMo m) = c.push m :=
  moLeaf_chars "mo" _ m c

theorem toList_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = true) :
    a.toList = [] := by
  have hs : a.size = 0 := by simpa [Array.isEmpty] using h
  have := a.length_toList
  rw [hs] at this
  exact List.eq_nil_of_length_eq_zero this

theorem cancelNode_chars (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (struck vals : Array Html.Node) (shown : Bool) (c : Array Char) :
    nodeChars c (cancelNode mk disp mark spec struck vals shown)
      = if mark == .to || shown then nodeListChars (nodeListChars c struck.toList) vals.toList
        else nodeListChars c struck.toList := by
  unfold cancelNode
  cases hm : mark == .to <;> cases shown <;> cases spec.room <;>
    simp [nodeChars, nodeListChars, Array.toList_push, nodeListChars_append]

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

theorem cancelPolygons_chars (ink : String) (pad : Int)
    (ps : List (Array (Int × Int))) (c : Array Char) :
    nodeListChars c (ps.map (cancelPolygon ink pad)) = c := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [cancelPolygon, nodeChars, nodeListChars] using ih

theorem measuredCancelNode_chars (mk : Marks) (metric : CancelMetric)
    (mark : CancelMark) (spec : CancelSpec) (struck vals : Array Html.Node)
    (shown : Bool) (c : Array Char) :
    nodeChars c (measuredCancelNode mk metric mark spec struck vals shown) =
      if mark == .to || shown then nodeListChars (nodeListChars c struck.toList) vals.toList
      else nodeListChars c struck.toList := by
  cases hm : mark == .to <;> cases shown <;> cases spec.room <;>
    simp [measuredCancelNode, hm, cancelAt, nodeChars, nodeListChars,
      Array.toList_map, paint_chars, cancelPolygons_chars]

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

theorem fracNode_chars (mk : Marks) (disp : Bool) (spec : FracSpec)
    (num den : Array Html.Node) (c : Array Char) :
    nodeChars c (fracNode mk disp spec num den) =
      let opened := match spec.left with | some ch => c.push ch | none => c
      let withBar := nodeListChars (nodeListChars opened num.toList) den.toList
      match spec.right with | some ch => withBar.push ch | none => withBar := by
  rcases spec with ⟨l, r, rule, style⟩
  cases l <;> cases r <;> cases style <;>
    simp [fracNode, fracKids, nodeChars, nodeListChars, sizedMo, pushChars_charText]

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
    show nodeListChars c (listNodes mk disp (some (inkCss mk.literal co n)) acc rest).toList
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
  | .word _, c => by simp only [nucNode]; split <;> rfl
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

/-- The MathML projection drops no glyph and invents none: its leaf text is the glyph-text fold of
the math list, which `mathmlChecks` holds to the PDF census, overline excepted. -/
public theorem mathml_glyphs_agree (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) :
    nodeChars #[] (formula display extra body mk) = listChars #[] body := by
  simp only [formula, formulaKids, nodeChars]
  rw [listNodes_chars _ display none body #[] #[]]
  rfl

/-- The in-context row paints the same glyph text as the root. -/
public theorem formulaRow_glyphs_agree (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) :
    nodeChars #[] (formulaRow display extra body mk) = listChars #[] body := by
  simp only [formulaRow, formulaKids, nodeChars]
  rw [listNodes_chars _ display none body #[] #[]]
  rfl

/-- The projection of the shared alphabet pass: MathML leaf text is the resolved list's glyph
text. -/
public theorem resolveMathAlphas_html_agree (coverage : Math.MathAlphabetCoverage)
    (display : Bool) (extra : Array (String × String)) (body : MList)
    (mk : Marks) :
    nodeChars #[]
      (formula display extra (Math.resolveMathAlphas coverage body) mk) =
      listChars #[] (Math.resolveMathAlphas coverage body) :=
  mathml_glyphs_agree display extra (Math.resolveMathAlphas coverage body) mk

mutual

/-- No element of the tree carries a tag `p` selects. -/
@[expose] public def tagFree (p : String → Bool) : Html.Node → Bool
  | .text _ => true
  | .elem t _ kids => !p t && tagFreeList p kids.toList
  | .style _ => true
  | .script _ _ => true

/-- `tagFree` over a list of trees. -/
@[expose] public def tagFreeList (p : String → Bool) : List Html.Node → Bool
  | [] => true
  | n :: rest => tagFree p n && tagFreeList p rest

end

mutual

/-- No `math` element stands inside another (MathML Core §2.1.1). -/
@[expose] public def unnested : Html.Node → Bool
  | .elem t _ kids =>
    if t == "math" then tagFreeList (· == "math") kids.toList else unnestedList kids.toList
  | .text _ => true
  | .style _ => true
  | .script _ _ => true

/-- `unnested` over a list of trees. -/
@[expose] public def unnestedList : List Html.Node → Bool
  | [] => true
  | n :: rest => unnested n && unnestedList rest

end

/-- Every element the content emitter builds but `merror`; `math` is not among them. -/
public def contentTags : List String :=
  ["mi", "mn", "mo", "mtext", "mspace", "mrow", "mstyle", "mpadded", "mfrac", "msqrt",
    "mroot", "msub", "msup", "msubsup", "munder", "mover", "munderover", "mtable", "mtr",
    "mtd", "svg", "polygon"]

public theorem tagFreeList_append (p : String → Bool) (l1 l2 : List Html.Node) :
    tagFreeList p (l1 ++ l2) = (tagFreeList p l1 && tagFreeList p l2) := by
  induction l1 with
  | nil => simp [tagFreeList]
  | cons n rest ih => simp [tagFreeList, ih, Bool.and_assoc]

public theorem tagFreeList_push (p : String → Bool) (acc : Array Html.Node) (n : Html.Node) :
    tagFreeList p (acc.push n).toList = (tagFreeList p acc.toList && tagFree p n) := by
  simp [Array.toList_push, tagFreeList_append, tagFreeList]

mutual

public theorem unnested_of_mathFree :
    ∀ n : Html.Node, tagFree (· == "math") n = true → unnested n = true
  | .text _, _ => rfl
  | .elem t _ kids, h => by
    simp only [tagFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [unnested, h.1, Bool.false_eq_true, ↓reduceIte]
    exact unnestedList_of_mathFree kids.toList h.2
  | .style _, _ => rfl
  | .script _ _, _ => rfl

public theorem unnestedList_of_mathFree :
    ∀ ns : List Html.Node, tagFreeList (· == "math") ns = true → unnestedList ns = true
  | [], _ => rfl
  | n :: rest, h => by
    simp only [tagFreeList, Bool.and_eq_true] at h
    simp only [unnestedList, unnested_of_mathFree n h.1, unnestedList_of_mathFree rest h.2,
      Bool.and_self]

end

theorem tagFree_paint (p : String → Bool) (ink : Option String) (n : Html.Node) :
    tagFree p (paint ink n) = tagFree p n := by
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

theorem leafTag_mem (cls : MathClass) (c : Char) : leafTag cls c ∈ contentTags := by
  cases cls <;> simp only [leafTag] <;> (try split) <;> simp [contentTags]

theorem contentTags_beq_false {s : String} (hs : s ∉ contentTags) :
    ∀ t ∈ contentTags, (t == s) = false := by
  intro t ht
  simp only [beq_eq_false_iff_ne]
  rintro rfl
  exact hs ht

theorem contentTags_false {p : String → Bool} (hp : ∀ t ∈ contentTags, p t = false) :
    p "mi" = false ∧ p "mn" = false ∧ p "mo" = false ∧ p "mtext" = false ∧
    p "mspace" = false ∧ p "mrow" = false ∧ p "mstyle" = false ∧ p "mpadded" = false ∧
    p "mfrac" = false ∧ p "msqrt" = false ∧ p "mroot" = false ∧ p "msub" = false ∧
    p "msup" = false ∧ p "msubsup" = false ∧ p "munder" = false ∧ p "mover" = false ∧
    p "munderover" = false ∧ p "mtable" = false ∧ p "mtr" = false ∧ p "mtd" = false ∧
    p "svg" = false ∧ p "polygon" = false := by
  refine ⟨hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_,
    hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_,
    hp _ ?_, hp _ ?_, hp _ ?_, hp _ ?_⟩ <;> simp [contentTags]

section
variable (p : String → Bool) (hp : ∀ t ∈ contentTags, p t = false)
include hp

theorem leafNode_tagFree (cls : MathClass) (c : Char) (attrs : Array (String × String))
    (kids : Array Html.Node) (hk : tagFreeList p kids.toList = true) :
    tagFree p (.elem (leafTag cls c) attrs kids) = true := by
  simp [tagFree, hp _ (leafTag_mem cls c), hk]

theorem scriptNode_tagFree (limits : Bool) (base : Html.Node) (sub sup : Array Html.Node)
    (subAttrs supAttrs : Array (String × String)) (hb : tagFree p base = true)
    (hs : tagFreeList p sub.toList = true) (hu : tagFreeList p sup.toList = true) :
    tagFree p (scriptNode limits base sub sup subAttrs supAttrs) = true := by
  unfold scriptNode
  cases limits <;> cases sup.isEmpty <;> cases sub.isEmpty <;>
    simp [tagFree, tagFreeList, hb, hs, hu, contentTags_false hp]

theorem radNode_tagFree (body deg : Array Html.Node) (degAttrs : Array (String × String))
    (hb : tagFreeList p body.toList = true) (hd : tagFreeList p deg.toList = true) :
    tagFree p (radNode body deg degAttrs) = true := by
  unfold radNode
  cases deg.isEmpty <;> simp [tagFree, tagFreeList, hb, hd, contentTags_false hp]

theorem fracNode_tagFree (mk : Marks) (disp : Bool) (spec : FracSpec)
    (num den : Array Html.Node) (hn : tagFreeList p num.toList = true)
    (hd : tagFreeList p den.toList = true) :
    tagFree p (fracNode mk disp spec num den) = true := by
  rcases spec with ⟨l, r, rule, style⟩
  cases l <;> cases r <;> cases style <;>
    simp [fracNode, fracKids, sizedMo, tagFree, tagFreeList, hn, hd, contentTags_false hp]

theorem accentNode_tagFree (mark : Char) (stretch : Bool) (body : Array Html.Node)
    (hb : tagFreeList p body.toList = true) :
    tagFree p (accentNode mark stretch body) = true := by
  cases h : mark == '̅' <;>
    simp [accentNode, h, tagFree, tagFreeList, hb, contentTags_false hp]

theorem cancelNode_tagFree (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (struck vals : Array Html.Node) (shown : Bool) (hs : tagFreeList p struck.toList = true)
    (hv : tagFreeList p vals.toList = true) :
    tagFree p (cancelNode mk disp mark spec struck vals shown) = true := by
  unfold cancelNode
  cases hm : mark == .to <;> cases shown <;> cases spec.room <;>
    simp [tagFree, tagFreeList, tagFreeList_append, hs, hv, contentTags_false hp]

theorem delimMo_tagFree (c : Char) : tagFree p (delimMo c) = true := by
  simp [delimMo, tagFree, tagFreeList, contentTags_false hp]

theorem cancelPolygons_tagFree (ink : String) (pad : Int) (ps : List (Array (Int × Int))) :
    tagFreeList p (ps.map (cancelPolygon ink pad)) = true := by
  induction ps with
  | nil => rfl
  | cons q ps ih => simp [cancelPolygon, tagFree, tagFreeList, ih, contentTags_false hp]

theorem measuredCancelNode_tagFree (mk : Marks) (metric : CancelMetric) (mark : CancelMark)
    (spec : CancelSpec) (struck vals : Array Html.Node) (shown : Bool)
    (hs : tagFreeList p struck.toList = true) (hv : tagFreeList p vals.toList = true) :
    tagFree p (measuredCancelNode mk metric mark spec struck vals shown) = true := by
  cases hm : mark == .to <;> cases shown <;>
    simp [measuredCancelNode, hm, cancelAt, tagFree, tagFreeList, tagFree_paint,
      Array.toList_map, cancelPolygons_tagFree p hp, hs, hv, contentTags_false hp]

theorem cancelWithMetric_tagFree (mk : Marks) (disp : Bool) (mark : CancelMark)
    (spec : CancelSpec) (body value : MList) (struck vals : Array Html.Node) (shown : Bool)
    (hs : tagFreeList p struck.toList = true) (hv : tagFreeList p vals.toList = true) :
    tagFree p (cancelWithMetric mk disp mark spec body value struck vals shown) = true := by
  unfold cancelWithMetric
  split
  · split
    · exact measuredCancelNode_tagFree p hp _ _ _ _ _ _ _ hs hv
    · exact cancelNode_tagFree p hp _ _ _ _ _ _ _ hs hv
  · exact cancelNode_tagFree p hp _ _ _ _ _ _ _ hs hv

end

private theorem alphaFree_cons {x : MItem} {rest : MList}
    (h : (MList.cons x rest).alphaFree = true) : x.alphaFree = true ∧ rest.alphaFree = true := by
  simpa [MList.alphaFree] using h

private theorem alphaFree_atom {cls : MathClass} {nuc : MNucleus} {sup sub : MList}
    {lim : Bool} (h : (MItem.atom cls nuc sup sub lim).alphaFree = true) :
    nuc.alphaFree = true ∧ sup.alphaFree = true ∧ sub.alphaFree = true := by
  simpa [MItem.alphaFree] using h

mutual

theorem listNodes_tagFree (p : String → Bool) (hp : ∀ t ∈ contentTags, p t = false)
    (mk : Marks) (disp : Bool) :
    ∀ (ink : Option String) (ml : MList) (acc : Array Html.Node),
      (p "merror" = true → ml.alphaFree = true) →
      tagFreeList p acc.toList = true →
      tagFreeList p (listNodes mk disp ink acc ml).toList = true
  | _, .nil, _, _, ha => ha
  | _, .cons (.ink co n) rest, acc, hm, ha =>
    listNodes_tagFree p hp mk disp _ rest acc (fun h => (alphaFree_cons (hm h)).2) ha
  | ink, .cons (.space mu) rest, acc, hm, ha => by
    show tagFreeList p (listNodes mk disp ink
      (acc.push (paint ink (itemNode mk disp (.space mu)))) rest).toList = true
    apply listNodes_tagFree p hp mk disp ink rest _ (fun h => (alphaFree_cons (hm h)).2)
    rw [tagFreeList_push, tagFree_paint, ha,
      itemNode_tagFree p hp mk disp (.space mu) (fun _ => rfl)]
    rfl
  | ink, .cons (.atom cls nuc sup sub lim) rest, acc, hm, ha => by
    show tagFreeList p (listNodes mk disp ink
      (acc.push (paint ink (itemNode mk disp (.atom cls nuc sup sub lim)))) rest).toList = true
    apply listNodes_tagFree p hp mk disp ink rest _ (fun h => (alphaFree_cons (hm h)).2)
    rw [tagFreeList_push, tagFree_paint, ha,
      itemNode_tagFree p hp mk disp _ (fun h => (alphaFree_cons (hm h)).1)]
    rfl

theorem itemNode_tagFree (p : String → Bool) (hp : ∀ t ∈ contentTags, p t = false)
    (mk : Marks) (disp : Bool) :
    ∀ (x : MItem), (p "merror" = true → x.alphaFree = true) →
      tagFree p (itemNode mk disp x) = true
  | .space _, _ => by simp [itemNode, tagFree, tagFreeList, contentTags_false hp]
  | .ink _ _, _ => by simp [itemNode, tagFree, tagFreeList, contentTags_false hp]
  | .atom cls nuc sup sub lim, hm => by
    show tagFree p (scriptNode (lim && disp) (nucNode mk disp cls nuc)
        (listNodes { mk with style := mk.style.sub } false none #[] sub)
        (listNodes { mk with style := mk.style.sup } false none #[] sup) _ _) = true
    exact scriptNode_tagFree p hp _ _ _ _ _ _
      (nucNode_tagFree p hp mk disp cls nuc (fun h => (alphaFree_atom (hm h)).1))
      (listNodes_tagFree p hp _ false none sub #[] (fun h => (alphaFree_atom (hm h)).2.2) rfl)
      (listNodes_tagFree p hp _ false none sup #[] (fun h => (alphaFree_atom (hm h)).2.1) rfl)

theorem nucNode_tagFree (p : String → Bool) (hp : ∀ t ∈ contentTags, p t = false)
    (mk : Marks) (disp : Bool) (cls : MathClass) :
    ∀ (nuc : MNucleus), (p "merror" = true → nuc.alphaFree = true) →
      tagFree p (nucNode mk disp cls nuc) = true
  | .sym c, _ => by
    simp only [nucNode]
    exact leafNode_tagFree p hp cls c _ _ rfl
  | .styled _ c, _ => by
    simp only [nucNode]
    exact leafNode_tagFree p hp cls c _ _ rfl
  | .word _, _ => by
    simp only [nucNode]
    split <;> simp [tagFree, tagFreeList, contentTags_false hp]
  | .list body, hm => by
    simp only [nucNode, tagFree, hp "mrow" (by simp [contentTags]), Bool.not_false,
      Bool.true_and]
    exact listNodes_tagFree p hp mk disp none body #[]
      (fun h => by simpa [MNucleus.alphaFree] using hm h) rfl
  | .alpha _ _ body, hm => by
    have hne : p "merror" = false := by
      cases h : p "merror" with
      | false => rfl
      | true => simpa [MNucleus.alphaFree] using hm h
    simp only [nucNode, tagFree, hne, Bool.not_false, Bool.true_and]
    exact listNodes_tagFree p hp mk disp none body #[] (fun h => by simp [hne] at h) rfl
  | .frac spec num den, hm => by
    have hf := hm
    simp only [nucNode]
    exact fracNode_tagFree p hp _ _ _ _ _
      (listNodes_tagFree p hp _ false none num #[]
        (fun h => by simp [MNucleus.alphaFree] at hf; exact (hf h).1) rfl)
      (listNodes_tagFree p hp _ false none den #[]
        (fun h => by simp [MNucleus.alphaFree] at hf; exact (hf h).2) rfl)
  | .rad deg body, hm => by
    have hf := hm
    simp only [nucNode]
    exact radNode_tagFree p hp _ _ _
      (listNodes_tagFree p hp _ disp none body #[]
        (fun h => by simp [MNucleus.alphaFree] at hf; exact (hf h).2) rfl)
      (listNodes_tagFree p hp _ false none deg #[]
        (fun h => by simp [MNucleus.alphaFree] at hf; exact (hf h).1) rfl)
  | .delim l r body, hm => by
    have hbody : p "merror" = true → body.alphaFree = true :=
      fun h => by simpa [MNucleus.alphaFree] using hm h
    have hmrow := hp "mrow" (by simp [contentTags])
    cases l with
    | none =>
      have hb := listNodes_tagFree p hp mk disp none body #[] hbody rfl
      cases r <;> simp only [nucNode, tagFree, tagFreeList_push, hb, delimMo_tagFree p hp,
        hmrow, Bool.not_false, Bool.and_true]
    | some c =>
      have hb := listNodes_tagFree p hp mk disp none body #[delimMo c] hbody
        (by simp [tagFreeList, delimMo_tagFree p hp])
      cases r <;> simp only [nucNode, tagFree, tagFreeList_push, hb, delimMo_tagFree p hp,
        hmrow, Bool.not_false, Bool.and_true]
  | .big d _, _ => by
    cases d <;> simp [nucNode, sizedMo, tagFree, tagFreeList, contentTags_false hp]
  | .accent mark stretch body, hm => by
    simp only [nucNode]
    exact accentNode_tagFree p hp _ _ _
      (listNodes_tagFree p hp _ disp none body #[]
        (fun h => by simpa [MNucleus.alphaFree] using hm h) rfl)
  | .grid kind rows, hm => by
    simp only [nucNode, tagFree, hp "mtable" (by simp [contentTags]), Bool.not_false,
      Bool.true_and]
    exact rowsNodes_tagFree p hp _ _ kind rows #[]
      (fun h => by simpa [MNucleus.alphaFree] using hm h) rfl
  | .cancel mark spec value body, hm => by
    have hf := hm
    simp only [nucNode]
    exact cancelWithMetric_tagFree p hp _ _ _ _ _ _ _ _ _
      (listNodes_tagFree p hp _ disp none body #[]
        (fun h => by simp [MNucleus.alphaFree] at hf; exact (hf h).2) rfl)
      (listNodes_tagFree p hp _ _ none value #[]
        (fun h => by simp [MNucleus.alphaFree] at hf; exact (hf h).1) rfl)

theorem rowNodes_tagFree (p : String → Bool) (hp : ∀ t ∈ contentTags, p t = false)
    (mk : Marks) (disp : Bool) (kind : GridKind) :
    ∀ (row : MRow) (k : Nat) (acc : Array Html.Node),
      (p "merror" = true → row.alphaFree = true) →
      tagFreeList p acc.toList = true →
      tagFreeList p (rowNodes mk disp kind k acc row).toList = true
  | .nil, _, _, _, ha => ha
  | .cons cell rest, k, acc, hm, ha => by
    have hf := hm
    simp only [rowNodes]
    apply rowNodes_tagFree p hp mk disp kind rest (k + 1) _
      (fun h => by simp [MRow.alphaFree] at hf; exact (hf h).2)
    rw [tagFreeList_push, ha]
    simp only [tagFree, hp "mtd" (by simp [contentTags]), Bool.not_false, Bool.true_and]
    exact listNodes_tagFree p hp mk disp none cell #[]
      (fun h => by simp [MRow.alphaFree] at hf; exact (hf h).1) rfl

theorem rowsNodes_tagFree (p : String → Bool) (hp : ∀ t ∈ contentTags, p t = false)
    (mk : Marks) (disp : Bool) (kind : GridKind) :
    ∀ (rows : MRows) (acc : Array Html.Node),
      (p "merror" = true → rows.alphaFree = true) →
      tagFreeList p acc.toList = true →
      tagFreeList p (rowsNodes mk disp kind acc rows).toList = true
  | .nil, _, _, ha => ha
  | .cons row rest, acc, hm, ha => by
    have hf := hm
    simp only [rowsNodes]
    apply rowsNodes_tagFree p hp mk disp kind rest _
      (fun h => by simp [MRows.alphaFree] at hf; exact (hf h).2)
    rw [tagFreeList_push, ha]
    simp only [tagFree, hp "mtr" (by simp [contentTags]), Bool.not_false, Bool.true_and]
    exact rowNodes_tagFree p hp mk disp kind row 0 #[]
      (fun h => by simp [MRows.alphaFree] at hf; exact (hf h).1) rfl

end

/-- A fact of the artifact: a formula's content holds no `math` element. -/
public theorem formulaKids_mathFree_contract (display : Bool) (body : MList) (mk : Marks) :
    tagFreeList (· == "math") (formulaKids display body mk).toList = true :=
  listNodes_tagFree (· == "math") (contentTags_beq_false (by simp [contentTags]))
    _ _ none body #[] (fun h => by simp at h) rfl

/-- A fact of the artifact: a formula's root is its tree's only root. -/
public theorem formula_unnested_contract (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) : unnested (formula display extra body mk) = true := by
  simp only [formula, unnested, beq_self_eq_true, ↓reduceIte]
  exact formulaKids_mathFree_contract display body mk

/-- A fact of the artifact: a formula row holds no `math` element. -/
public theorem formulaRow_mathFree_contract (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) :
    tagFree (· == "math") (formulaRow display extra body mk) = true := by
  simp only [formulaRow, tagFree, formulaKids_mathFree_contract, Bool.and_true]
  rfl

/-- The MathML projection of `Math.resolveMathAlphas_covers`: a resolved formula emits no
`merror`. -/
public theorem formula_merrorFree_contract (display : Bool) (body : MList) (mk : Marks)
    (h : body.alphaFree = true) :
    tagFreeList (· == "merror") (formulaKids display body mk).toList = true :=
  listNodes_tagFree (· == "merror") (contentTags_beq_false (by simp [contentTags]))
    _ _ none body #[] (fun _ => h) rfl

/-- Whether a style's last declaration is `keepLineCss`, the one CSS reads last. -/
@[expose] public def keepsValue (v : String) : Bool :=
  v == keepLineCss || ("; " ++ keepLineCss).toList.isSuffixOf v.toList

/-- Whether an element's style keeps its line (`keepsValue`). -/
@[expose] public def keepsLine (attrs : Array (String × String)) : Bool :=
  attrs.any fun (k, v) => k == "style" && keepsValue v

mutual

/-- Every text of the tree longer than one scalar stands under an element keeping its line. -/
@[expose] public def linesHeld : Html.Node → Bool
  | .text s => decide (s.length ≤ 1)
  | .elem _ attrs kids => keepsLine attrs || linesHeldList kids.toList
  | .style _ => true
  | .script _ _ => true

/-- `linesHeld` over a list of trees. -/
@[expose] public def linesHeldList : List Html.Node → Bool
  | [] => true
  | n :: rest => linesHeld n && linesHeldList rest

end

public theorem linesHeldList_append (l1 l2 : List Html.Node) :
    linesHeldList (l1 ++ l2) = (linesHeldList l1 && linesHeldList l2) := by
  induction l1 with
  | nil => simp [linesHeldList]
  | cons n rest ih => simp [linesHeldList, ih, Bool.and_assoc]

public theorem linesHeldList_push (acc : Array Html.Node) (n : Html.Node) :
    linesHeldList (acc.push n).toList = (linesHeldList acc.toList && linesHeld n) := by
  simp [Array.toList_push, linesHeldList_append, linesHeldList]

theorem charText_held (t : String) (attrs : Array (String × String)) (c : Char) :
    linesHeld (.elem t attrs #[.text (charText c)]) = true := by
  simp [linesHeld, linesHeldList, charText]

theorem keepsLine_push (attrs : Array (String × String)) (a : String × String)
    (h : keepsLine attrs = true) : keepsLine (attrs.push a) = true := by
  unfold keepsLine at h ⊢
  rw [Array.any_push, h, Bool.true_or]

public theorem keepsValue_tint (pre v : String) (h : keepsValue v = true) :
    keepsValue (pre ++ "; " ++ v) = true := by
  unfold keepsValue at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq, List.isSuffixOf_iff_suffix] at h ⊢
  right
  rcases h with rfl | hs
  · simp only [String.toList_append, List.append_assoc]
    exact List.suffix_append _ _
  · simp only [String.toList_append, List.append_assoc] at hs ⊢
    exact hs.trans ((List.suffix_append _ _).trans (List.suffix_append _ _))

theorem keepsLine_modify (attrs : Array (String × String)) (i : Nat)
    (f : String × String → String × String)
    (hf : ∀ p, (f p).1 = p.1 ∧ (keepsValue p.2 = true → keepsValue (f p).2 = true))
    (h : keepsLine attrs = true) :
    keepsLine (attrs.modify i f) = true := by
  simp only [keepsLine, Array.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨j, hj, hk, hs⟩ := h
  refine ⟨j, by simpa using hj, ?_⟩
  rw [Array.getElem_modify]
  split
  · exact ⟨(hf _).1.trans hk, (hf _).2 hs⟩
  · exact ⟨hk, hs⟩

theorem paint_held (ink : Option String) (n : Html.Node) (h : linesHeld n = true) :
    linesHeld (paint ink n) = true := by
  cases n with
  | elem t attrs kids =>
    cases ink with
    | none => exact h
    | some css =>
      simp only [linesHeld, Bool.or_eq_true] at h
      simp only [paint]
      split
      · simp only [linesHeld, Bool.or_eq_true]
        refine h.imp (keepsLine_modify attrs _ _ ?_) id
        intro p
        exact ⟨rfl, keepsValue_tint _ _⟩
      · simp only [linesHeld, Bool.or_eq_true]
        exact h.imp (keepsLine_push attrs _) id
  | text s => exact h
  | style s => exact h
  | script a j => exact h

theorem scriptNode_held (limits : Bool) (base : Html.Node) (sub sup : Array Html.Node)
    (subAttrs supAttrs : Array (String × String)) (hb : linesHeld base = true)
    (hs : linesHeldList sub.toList = true) (hu : linesHeldList sup.toList = true) :
    linesHeld (scriptNode limits base sub sup subAttrs supAttrs) = true := by
  unfold scriptNode
  cases limits <;> cases sup.isEmpty <;> cases sub.isEmpty <;>
    simp [linesHeld, linesHeldList, hb, hs, hu]

theorem radNode_held (body deg : Array Html.Node) (degAttrs : Array (String × String))
    (hb : linesHeldList body.toList = true) (hd : linesHeldList deg.toList = true) :
    linesHeld (radNode body deg degAttrs) = true := by
  unfold radNode
  cases deg.isEmpty <;> simp [linesHeld, linesHeldList, hb, hd]

theorem fracNode_held (mk : Marks) (disp : Bool) (spec : FracSpec)
    (num den : Array Html.Node) (hn : linesHeldList num.toList = true)
    (hd : linesHeldList den.toList = true) :
    linesHeld (fracNode mk disp spec num den) = true := by
  rcases spec with ⟨l, r, rule, style⟩
  cases l <;> cases r <;> cases style <;>
    simp [fracNode, fracKids, sizedMo, linesHeld, linesHeldList, hn, hd, charText]

theorem accentNode_held (mark : Char) (stretch : Bool) (body : Array Html.Node)
    (hb : linesHeldList body.toList = true) :
    linesHeld (accentNode mark stretch body) = true := by
  cases h : mark == '̅' <;>
    simp [accentNode, h, linesHeld, linesHeldList, hb, charText]

theorem cancelNode_held (mk : Marks) (disp : Bool) (mark : CancelMark) (spec : CancelSpec)
    (struck vals : Array Html.Node) (shown : Bool) (hs : linesHeldList struck.toList = true)
    (hv : linesHeldList vals.toList = true) :
    linesHeld (cancelNode mk disp mark spec struck vals shown) = true := by
  unfold cancelNode
  cases hm : mark == .to <;> cases shown <;> cases spec.room <;>
    simp [linesHeld, linesHeldList, linesHeldList_append, hs, hv]

theorem cancelPolygons_held (ink : String) (pad : Int) (ps : List (Array (Int × Int))) :
    linesHeldList (ps.map (cancelPolygon ink pad)) = true := by
  induction ps with
  | nil => rfl
  | cons q ps ih => simp [cancelPolygon, linesHeld, linesHeldList, ih]

theorem measuredCancelNode_held (mk : Marks) (metric : CancelMetric) (mark : CancelMark)
    (spec : CancelSpec) (struck vals : Array Html.Node) (shown : Bool)
    (hs : linesHeldList struck.toList = true) (hv : linesHeldList vals.toList = true) :
    linesHeld (measuredCancelNode mk metric mark spec struck vals shown) = true := by
  have hp : ∀ ink : Option String, linesHeld (paint ink
      (.elem "mstyle" (relativeStyle mk (spec.size.style mk.style)) vals)) = true :=
    fun ink => paint_held ink _ (by simp [linesHeld, hv])
  cases hm : mark == .to <;> cases shown <;>
    simp [measuredCancelNode, hm, cancelAt, linesHeld, linesHeldList, Array.toList_map,
      cancelPolygons_held, hp, hs]

theorem cancelWithMetric_held (mk : Marks) (disp : Bool) (mark : CancelMark)
    (spec : CancelSpec) (body value : MList) (struck vals : Array Html.Node) (shown : Bool)
    (hs : linesHeldList struck.toList = true) (hv : linesHeldList vals.toList = true) :
    linesHeld (cancelWithMetric mk disp mark spec body value struck vals shown) = true := by
  unfold cancelWithMetric
  split
  · split
    · exact measuredCancelNode_held _ _ _ _ _ _ _ hs hv
    · exact cancelNode_held _ _ _ _ _ _ _ hs hv
  · exact cancelNode_held _ _ _ _ _ _ _ hs hv

theorem delimMo_held (c : Char) : linesHeld (delimMo c) = true :=
  charText_held _ _ c

mutual

theorem listNodes_held (mk : Marks) (disp : Bool) :
    ∀ (ink : Option String) (ml : MList) (acc : Array Html.Node),
      linesHeldList acc.toList = true →
      linesHeldList (listNodes mk disp ink acc ml).toList = true
  | _, .nil, _, ha => ha
  | _, .cons (.ink co n) rest, acc, ha => listNodes_held mk disp _ rest acc ha
  | ink, .cons (.space mu) rest, acc, ha => by
    show linesHeldList (listNodes mk disp ink
      (acc.push (paint ink (itemNode mk disp (.space mu)))) rest).toList = true
    apply listNodes_held mk disp ink rest
    rw [linesHeldList_push, ha, paint_held ink _ (itemNode_held mk disp (.space mu))]
    rfl
  | ink, .cons (.atom cls nuc sup sub lim) rest, acc, ha => by
    show linesHeldList (listNodes mk disp ink
      (acc.push (paint ink (itemNode mk disp (.atom cls nuc sup sub lim)))) rest).toList = true
    apply listNodes_held mk disp ink rest
    rw [linesHeldList_push, ha, paint_held ink _ (itemNode_held mk disp _)]
    rfl

theorem itemNode_held (mk : Marks) (disp : Bool) :
    ∀ (x : MItem), linesHeld (itemNode mk disp x) = true
  | .space _ => by simp [itemNode, linesHeld, linesHeldList]
  | .ink _ _ => by simp [itemNode, linesHeld, linesHeldList]
  | .atom cls nuc sup sub lim => by
    show linesHeld (scriptNode (lim && disp) (nucNode mk disp cls nuc)
        (listNodes { mk with style := mk.style.sub } false none #[] sub)
        (listNodes { mk with style := mk.style.sup } false none #[] sup) _ _) = true
    exact scriptNode_held _ _ _ _ _ _ (nucNode_held mk disp cls nuc)
      (listNodes_held _ false none sub #[] rfl) (listNodes_held _ false none sup #[] rfl)

theorem nucNode_held (mk : Marks) (disp : Bool) (cls : MathClass) :
    ∀ (nuc : MNucleus), linesHeld (nucNode mk disp cls nuc) = true
  | .sym c => by
    simp only [nucNode]
    exact charText_held _ _ c
  | .styled _ c => by
    simp only [nucNode]
    exact charText_held _ _ c
  | .word _ => by
    simp only [nucNode]
    split <;> simp [linesHeld, keepsLine, keepsValue]
  | .list body => by
    simp only [nucNode, linesHeld]
    rw [listNodes_held mk disp none body #[] rfl, Bool.or_true]
  | .alpha _ _ body => by
    simp only [nucNode, linesHeld]
    rw [listNodes_held mk disp none body #[] rfl, Bool.or_true]
  | .frac spec num den => by
    simp only [nucNode]
    exact fracNode_held _ _ _ _ _ (listNodes_held _ false none num #[] rfl)
      (listNodes_held _ false none den #[] rfl)
  | .rad deg body => by
    simp only [nucNode]
    exact radNode_held _ _ _ (listNodes_held _ disp none body #[] rfl)
      (listNodes_held _ false none deg #[] rfl)
  | .delim l r body => by
    cases l with
    | none =>
      have hb := listNodes_held mk disp none body #[] rfl
      cases r <;> simp only [nucNode, linesHeld, linesHeldList_push, hb, delimMo_held,
        Bool.and_true, Bool.or_true]
    | some c =>
      have hb := listNodes_held mk disp none body #[delimMo c]
        (by simp [linesHeldList, delimMo_held])
      cases r <;> simp only [nucNode, linesHeld, linesHeldList_push, hb, delimMo_held,
        Bool.and_true, Bool.or_true]
  | .big d _ => by
    cases d <;> simp [nucNode, sizedMo, linesHeld, linesHeldList, charText]
  | .accent mark stretch body => by
    simp only [nucNode]
    exact accentNode_held _ _ _ (listNodes_held _ disp none body #[] rfl)
  | .grid kind rows => by
    simp only [nucNode, linesHeld]
    rw [rowsNodes_held _ _ kind rows #[] rfl, Bool.or_true]
  | .cancel mark spec value body => by
    simp only [nucNode]
    exact cancelWithMetric_held _ _ _ _ _ _ _ _ _
      (listNodes_held _ disp none body #[] rfl) (listNodes_held _ _ none value #[] rfl)

theorem rowNodes_held (mk : Marks) (disp : Bool) (kind : GridKind) :
    ∀ (row : MRow) (k : Nat) (acc : Array Html.Node),
      linesHeldList acc.toList = true →
      linesHeldList (rowNodes mk disp kind k acc row).toList = true
  | .nil, _, _, ha => ha
  | .cons cell rest, k, acc, ha => by
    simp only [rowNodes]
    apply rowNodes_held mk disp kind rest (k + 1)
    rw [linesHeldList_push, ha]
    simp only [linesHeld]
    rw [listNodes_held mk disp none cell #[] rfl, Bool.or_true, Bool.true_and]

theorem rowsNodes_held (mk : Marks) (disp : Bool) (kind : GridKind) :
    ∀ (rows : MRows) (acc : Array Html.Node),
      linesHeldList acc.toList = true →
      linesHeldList (rowsNodes mk disp kind acc rows).toList = true
  | .nil, _, ha => ha
  | .cons row rest, acc, ha => by
    simp only [rowsNodes]
    apply rowsNodes_held mk disp kind rest
    rw [linesHeldList_push, ha]
    simp only [linesHeld]
    rw [rowNodes_held mk disp kind row 0 #[] rfl, Bool.or_true, Bool.true_and]

end

/-- A fact of the artifact: a formula sets every text run longer than one scalar under a style
keeping its line, as TeX sets a word in one box. -/
public theorem formulaKids_linesHeld_contract (display : Bool) (body : MList) (mk : Marks) :
    linesHeldList (formulaKids display body mk).toList = true :=
  listNodes_held _ display none body #[] rfl

/-- A fact of the artifact: a formula's `math` element keeps the line of every text run it sets. -/
public theorem formula_linesHeld_contract (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) : linesHeld (formula display extra body mk) = true := by
  simp only [formula, linesHeld, formulaKids_linesHeld_contract, Bool.or_true]

/-- A fact of the artifact: a formula row keeps the line of every text run it sets. -/
public theorem formulaRow_linesHeld_contract (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) : linesHeld (formulaRow display extra body mk) = true := by
  simp only [formulaRow, linesHeld, formulaKids_linesHeld_contract, Bool.or_true]

end LeanTex.Core.MathMl
