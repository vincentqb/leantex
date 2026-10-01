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

/-- An `mspace` width: mu over 18ths of an em (TeXbook p. 168), printed in
milli-em. The width attribute is a presentational hint whose negative
values are invalid CSS (MathML Core §3.2.5), so `\!`'s negative kern
declares the honest floor 0 instead of an ignored attribute. -/
def muWidth (mu : Int) : String :=
  let m := max mu 0 * 1000 / 18
  let whole := m / 1000
  let frac := (m % 1000).toNat
  if frac == 0 then s!"{whole}em"
  else
    let fs := toString frac
    s!"{whole}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "em"

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

/-- A fraction's declared rule as `mfrac`'s `linethickness` (MathML Core
§3.3.2), in points to the thousandth; nothing for the face's own. -/
def ruleAttrs : Option Int → Array (String × String)
  | none => #[]
  | some t =>
    let m := max t 0 * 1000 / 65536
    let fs := toString (m % 1000)
    #[("linethickness", if m == 0 then "0"
      else s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "pt")]

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
    (sub sup : Array Html.Node) : Html.Node :=
  match sup.isEmpty, sub.isEmpty with
  | true, true => base
  | false, true =>
    .elem (if limits then "mover" else "msup") #[]
      #[base, .elem "mrow" #[] sup]
  | true, false =>
    .elem (if limits then "munder" else "msub") #[]
      #[base, .elem "mrow" #[] sub]
  | false, false =>
    .elem (if limits then "munderover" else "msubsup") #[]
      #[base, .elem "mrow" #[] sub, .elem "mrow" #[] sup]

/-- A radical: `msqrt` takes any number of children as an implied row,
`mroot` exactly the base then the index (MathML Core §3.3.3) — the
renderer draws the surd, so no U+221A glyph enters the tree, as none
enters `Math.MList.scalarsList`. -/
def radNode (body deg : Array Html.Node) : Html.Node :=
  match deg.isEmpty with
  | true => .elem "msqrt" #[] body
  | false =>
    .elem "mroot" #[]
      #[.elem "mrow" #[] body, .elem "mrow" #[] deg]

/-- What a formula's cancel marks read beyond the AST, in thousandths of an
em: the math face's overbar rule and clearance when the page ships its
faces — the two quantities the PDF lays the marks with — else TeX's own
stand-ins, plain TeX's default rule (0.4 pt at the 10 pt base, 40 per
mille) and rule 9's clearance of three rules. -/
structure Marks where
  rule : Nat := 40
  gap : Nat := 120
  deriving Repr, BEq, Inhabited

/-- A length in thousandths of an em, as CSS reads it. -/
def milliEm (m : Nat) : String :=
  let fs := toString (m % 1000)
  s!"{m / 1000}." ++ "".pushn '0' (3 - fs.length) ++ fs ++ "em"

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

/-- A cancel mark over its emitted struck row and value: CSS over the struck
row's padded box, the box the PDF strikes corner to corner — `padding` the
clearance, the gradient the band (`cancelBand`), and the arrowhead an empty
element placed at the box's top-right corner and turned along its diagonal
by the box itself (`offset-path` over the containing box, `offset-rotate`):
MathML Core has no `menclose`, and this needs no script. The value is the
row's superscript, a clearance from the head, in the style the package's
table names — a superscript steps one level down, which `smaller` keeps
except over a display base (text style there) and `samesize` never takes —
and in the marks' colour, as cancel.sty colours it. Overlapping
(cancel.sty's `overlap`), negative margins give the marks' room back and
the value takes none. -/
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
  let head := Html.Node.elem "mspace" #[("style", s!"position: absolute; left: 0; top: 0; \
width: {milliEm (4 * r)}; height: {milliEm (3 * r)}; background: {ink}; \
clip-path: polygon(0 0, 100% 50%, 0 100%); offset-path: shape(from 100% 0%, line to 0% 100%); \
offset-distance: 0%; offset-rotate: reverse; offset-anchor: 100% 50%; {print}")] #[]
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
  if mark == .to || shown then .elem "msup" #[] #[base, valueNode] else base

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
  | .space mu => .elem "mspace" #[("width", muWidth mu)] #[]
  | .ink _ _ => .elem "mrow" #[] #[]
  | .atom cls nuc sup sub lim =>
    scriptNode (lim && disp) (nucNode mk disp cls nuc)
      (listNodes mk false none #[] sub) (listNodes mk false none #[] sup)

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
    -- Unreachable on every public path: `resolveMathAlphas` eliminates each
    -- `.alpha` node before either backend (`resolveMathAlphas_covers`), and
    -- the driver and `HtmlDoc.emit` resolve first. A `.alpha` reaching here
    -- is a bypass of that door, so it is loud — a MathML `merror` naming the
    -- unresolved alphabet's content — never a silent `mrow` that would pass
    -- as ordinary math. The body still renders inside, so no content is lost.
    .elem "merror" #[] (listNodes mk disp none #[] body)
  | .frac spec num den =>
    let bar := Html.Node.elem "mfrac" (ruleAttrs spec.rule)
      #[.elem "mrow" #[] (listNodes mk false none #[] num),
        .elem "mrow" #[] (listNodes mk false none #[] den)]
    if spec.style.isNone && spec.left.isNone && spec.right.isNone then bar
    else .elem "mrow" (styleAttrs spec.style) (fracKids disp spec bar)
  | .rad deg body =>
    radNode (listNodes mk disp none #[] body) (listNodes mk false none #[] deg)
  | .delim l r body =>
    let opened := match l with
      | some c => #[delimMo c]
      | none => (#[] : Array Html.Node)
    let withBody := listNodes mk disp none opened body
    let closed := match r with
      | some c => withBody.push (delimMo c)
      | none => withBody
    .elem "mrow" #[] closed
  | .accent mark stretch body =>
    let base := Html.Node.elem "mrow" #[] (listNodes mk disp none #[] body)
    match mark == '\u0305' with
    | true =>
      .elem "mover" #[("accent", "false")]
        #[base, .elem "mo" #[("stretchy", "true")]
          #[.text (charText overlineChar)]]
    | false =>
      .elem "mover" #[("accent", "true")]
        #[base, .elem "mo" #[("stretchy", if stretch then "true" else "false")]
          #[.text (charText mark)]]
  | .grid kind rows =>
    let cellDisp := match kind with
      | .array _ _ => false
      | .align => true
      | .gather => true
    let attrs : Array (String × String) := match kind with
      | .array _ _ => #[]
      | .align => #[("displaystyle", "true")]
      | .gather => #[("displaystyle", "true")]
    .elem "mtable" attrs (rowsNodes mk cellDisp kind #[] rows)
  | .cancel mark spec value body =>
    cancelNode mk disp mark spec (listNodes mk disp none #[] body)
      (listNodes mk (spec.size == .same && disp) none #[] value) (value matches .cons _ _)

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
    (listNodes mk display none #[] body)

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
    (sub sup : Array Html.Node) (c : Array Char) :
    nodeChars c (scriptNode limits base sub sup)
      = nodeListChars (nodeListChars (nodeChars c base) sub.toList)
          sup.toList := by
  unfold scriptNode
  cases hsup : sup.isEmpty <;> cases hsub : sub.isEmpty
  · show nodeListChars c [base, .elem "mrow" #[] sub, .elem "mrow" #[] sup]
        = _
    rfl
  · rw [toList_of_isEmpty hsub]
    show nodeListChars c [base, .elem "mrow" #[] sup] = _
    rfl
  · rw [toList_of_isEmpty hsup]
    show nodeListChars c [base, .elem "mrow" #[] sub] = _
    rfl
  · rw [toList_of_isEmpty hsub, toList_of_isEmpty hsup]
    rfl

/-- A radical's text is its body then its degree, `msqrt` and `mroot`
alike. -/
theorem radNode_chars (body deg : Array Html.Node) (c : Array Char) :
    nodeChars c (radNode body deg)
      = nodeListChars (nodeListChars c body.toList) deg.toList := by
  unfold radNode
  cases hdeg : deg.isEmpty
  · show nodeListChars c [.elem "mrow" #[] body, .elem "mrow" #[] deg] = _
    rfl
  · rw [toList_of_isEmpty hdeg]
    rfl

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
        (listNodes mk false none #[] sub) (listNodes mk false none #[] sup))
      = listChars (listChars (nucChars c nuc) sub) sup
    rw [scriptNode_chars, nucNode_chars mk disp cls nuc c,
      listNodes_chars mk false none sub #[] (nucChars c nuc),
      listNodes_chars mk false none sup #[]]
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
  | .frac ⟨l, r, rule, style⟩ num den, c => by
    have bar : ∀ c', nodeListChars (nodeListChars c' (listNodes mk false none #[] num).toList)
        (listNodes mk false none #[] den).toList = listChars (listChars c' num) den := by
      intro c'
      rw [listNodes_chars mk false none num #[] c', listNodes_chars mk false none den #[]]
      rfl
    have mo : ∀ (m : Char) (s : String) (c' : Array Char),
        nodeChars c' (sizedMo m s) = c'.push m :=
      fun m s c' => moLeaf_chars "mo" _ m c'
    cases l <;> cases r <;> cases style <;>
      simp [nucNode, nucChars, fracKids, nodeChars, nodeListChars, bar, mo]
  | .rad deg body, c => by
    show nodeChars c (radNode (listNodes mk disp none #[] body)
        (listNodes mk false none #[] deg)) = listChars (listChars c body) deg
    rw [radNode_chars, listNodes_chars mk disp none body #[] c,
      listNodes_chars mk false none deg #[]]
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
  | .accent mark stretch body, c => by
    cases h : mark == '\u0305' <;> simp only [nucNode, nucChars, h]
    · show nodeChars
          (nodeListChars c (listNodes mk disp none #[] body).toList)
          (.elem "mo" #[("stretchy", if stretch then "true" else "false")]
            #[.text (charText mark)]) = _
      rw [listNodes_chars mk disp none body #[] c, moLeaf_chars]
      rfl
    · show nodeChars
          (nodeListChars c (listNodes mk disp none #[] body).toList)
          (.elem "mo" #[("stretchy", "true")]
            #[.text (charText overlineChar)]) = _
      rw [listNodes_chars mk disp none body #[] c, moLeaf_chars]
      rfl
  | .grid kind rows, c => by
    cases kind <;>
      simp only [nucNode, nucChars] <;>
      show nodeListChars c (rowsNodes mk _ _ #[] rows).toList = rowsChars c rows <;>
      rw [rowsNodes_chars] <;>
      rfl
  | .cancel mark spec value body, c => by
    show nodeChars c (cancelNode mk disp mark spec (listNodes mk disp none #[] body)
        (listNodes mk (spec.size == .same && disp) none #[] value) (value matches .cons _ _))
      = listChars (listChars c body) value
    have hs := listNodes_chars mk disp none body #[] c
    have hv := listNodes_chars mk (spec.size == .same && disp) none value #[]
    simp only [nodeListChars] at hs hv
    rw [cancelNode_chars, hs, hv]
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
a cancel mark's strike and arrowhead are CSS and an empty element, text of
neither; the fold's agreement with the PDF's coverage census
(`Math.MList.scalarsList` — same scalars, its order, overline excepted)
is pinned by test in `mathmlChecks`. -/
theorem mathml_glyphs_agree (display : Bool) (extra : Array (String × String))
    (body : MList) (mk : Marks) :
    nodeChars #[] (formula display extra body mk) = listChars #[] body := by
  simp only [formula, nodeChars]
  rw [listNodes_chars mk display none body #[] #[]]
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
