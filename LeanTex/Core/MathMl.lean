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

/-- A `\left`/`\right` delimiter: stretchy, and symmetric about the math
axis (`mo` attributes, MathML Core §3.2.4.2) — rule 19's centring, which
`Layout.delimAssemble` realizes on the PDF side. -/
def delimMo (c : Char) : Html.Node :=
  .elem "mo" #[("stretchy", "true"), ("symmetric", "true")]
    #[.text (charText c)]

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

mutual

/-- The MathML children of a math list, one element per item, onto `acc`. -/
def listNodes (disp : Bool) (acc : Array Html.Node) :
    MList → Array Html.Node
  | .nil => acc
  | .cons x rest => listNodes disp (acc.push (itemNode disp x)) rest

/-- One item as one element: an explicit space is `mspace`; an atom is its
nucleus under its script schema (`scriptNode`). `disp` goes false inside
scripts, as the script styles are never display. -/
def itemNode (disp : Bool) : MItem → Html.Node
  | .space mu => .elem "mspace" #[("width", muWidth mu)] #[]
  | .atom cls nuc sup sub lim =>
    scriptNode (lim && disp) (nucNode disp cls nuc)
      (listNodes false #[] sub) (listNodes false #[] sup)

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
def nucNode (disp : Bool) (cls : MathClass) : MNucleus → Html.Node
  | .sym c =>
    let tag := leafTag cls c
    .elem tag (if tag == "mi" then #[("mathvariant", "normal")] else #[])
      #[.text (charText c)]
  | .word s => .elem "mi" #[] #[.text s]
  | .list body => .elem "mrow" #[] (listNodes disp #[] body)
  | .frac num den =>
    .elem "mfrac" #[]
      #[.elem "mrow" #[] (listNodes false #[] num),
        .elem "mrow" #[] (listNodes false #[] den)]
  | .rad deg body =>
    radNode (listNodes disp #[] body) (listNodes false #[] deg)
  | .delim l r body =>
    let opened := match l with
      | some c => #[delimMo c]
      | none => (#[] : Array Html.Node)
    let withBody := listNodes disp opened body
    let closed := match r with
      | some c => withBody.push (delimMo c)
      | none => withBody
    .elem "mrow" #[] closed
  | .accent mark stretch body =>
    let base := Html.Node.elem "mrow" #[] (listNodes disp #[] body)
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
      | .array _ => false
      | .align => true
      | .gather => true
    let attrs : Array (String × String) := match kind with
      | .array _ => #[]
      | .align => #[("displaystyle", "true")]
      | .gather => #[("displaystyle", "true")]
    .elem "mtable" attrs (rowsNodes cellDisp kind #[] rows)

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
def rowNodes (disp : Bool) (kind : GridKind) (k : Nat)
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
      | .array _, .center => #[]
      | .array _, .left => #[("style", "text-align: left")]
      | .array _, .right =>
        #[("style", "text-align: right; text-align: -webkit-right")]
    rowNodes disp kind (k + 1)
      (acc.push (.elem "mtd" attrs (listNodes disp #[] cell))) rest

/-- The `mtr` rows of a grid. -/
def rowsNodes (disp : Bool) (kind : GridKind) (acc : Array Html.Node) :
    MRows → Array Html.Node
  | .nil => acc
  | .cons row rest =>
    rowsNodes disp kind
      (acc.push (.elem "mtr" #[] (rowNodes disp kind 0 #[] row))) rest

end

/-- One formula as its `math` element: `display="block"` for display math
(the user-agent stylesheet then gives it `math-style: normal` and centres
the content box — MathML Core §2.1.1), absent for inline, which the same
stylesheet treats as `inline`. The backend's own attributes (class,
`data-tex`) ride in `extra`. -/
def formula (display : Bool) (extra : Array (String × String))
    (body : MList) : Html.Node :=
  .elem "math"
    ((if display then #[("display", "block")] else #[]) ++ extra)
    (listNodes display #[] body)

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
  | .atom _ nuc sup sub _ =>
    listChars (listChars (nucChars acc nuc) sub) sup

def nucChars (acc : Array Char) : MNucleus → Array Char
  | .sym c => acc.push c
  | .word s => pushChars acc s.toList
  | .list body => listChars acc body
  | .frac num den => listChars (listChars acc num) den
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

/-- An emitted list grows the accumulator: one element per item, none
removed — the fact that lets `scriptNode` and `radNode` read `.nil`
(no script, no degree) off an empty child array. -/
theorem listNodes_size (disp : Bool) :
    ∀ (ml : MList) (acc : Array Html.Node),
      acc.size ≤ (listNodes disp acc ml).size
  | .nil, _ => Nat.le_refl _
  | .cons x rest, acc =>
    Nat.le_trans (by simp)
      (listNodes_size disp rest (acc.push (itemNode disp x)))

/-- An empty emission is an empty list, on the fold: the glyph text of a
list whose emission is empty is the accumulator unchanged. -/
theorem listChars_of_empty (disp : Bool) (ml : MList)
    (h : (listNodes disp #[] ml).isEmpty = true) (c : Array Char) :
    listChars c ml = c := by
  cases ml with
  | nil => rfl
  | cons x rest =>
    exfalso
    have hs := listNodes_size disp rest #[itemNode disp x]
    have h0 : (listNodes disp #[itemNode disp x] rest).size = 0 := by
      simpa [listNodes, Array.isEmpty_iff_size_eq_zero] using h
    have h1 : (#[itemNode disp x] : Array Html.Node).size = 1 := rfl
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

theorem listNodes_chars (disp : Bool) :
    ∀ (ml : MList) (acc : Array Html.Node) (c : Array Char),
      nodeListChars c (listNodes disp acc ml).toList
        = listChars (nodeListChars c acc.toList) ml
  | .nil, acc, c => rfl
  | .cons x rest, acc, c => by
    show nodeListChars c (listNodes disp (acc.push (itemNode disp x)) rest).toList
        = listChars (itemChars (nodeListChars c acc.toList) x) rest
    rw [listNodes_chars disp rest, Array.toList_push, nodeListChars_append]
    simp only [nodeListChars]
    rw [itemNode_chars disp x]

theorem itemNode_chars (disp : Bool) :
    ∀ (x : MItem) (c : Array Char),
      nodeChars c (itemNode disp x) = itemChars c x
  | .space _, c => rfl
  | .atom cls nuc sup sub lim, c => by
    show nodeChars c (scriptNode (lim && disp) (nucNode disp cls nuc)
        (listNodes false #[] sub) (listNodes false #[] sup))
      = listChars (listChars (nucChars c nuc) sub) sup
    rw [scriptNode_chars, nucNode_chars disp cls nuc c,
      listNodes_chars false sub #[] (nucChars c nuc),
      listNodes_chars false sup #[]]
    rfl

theorem nucNode_chars (disp : Bool) (cls : MathClass) :
    ∀ (nuc : MNucleus) (c : Array Char),
      nodeChars c (nucNode disp cls nuc) = nucChars c nuc
  | .sym ch, c => by
    show pushChars c (charText ch).toList = c.push ch
    exact pushChars_charText c ch
  | .word _, c => rfl
  | .list body, c => by
    show nodeListChars c (listNodes disp #[] body).toList = listChars c body
    rw [listNodes_chars disp body #[] c]
    rfl
  | .frac num den, c => by
    show nodeChars
        (nodeChars c (.elem "mrow" #[] (listNodes false #[] num)))
        (.elem "mrow" #[] (listNodes false #[] den))
      = listChars (listChars c num) den
    show nodeListChars
        (nodeListChars c (listNodes false #[] num).toList)
        (listNodes false #[] den).toList = _
    rw [listNodes_chars false num #[] c, listNodes_chars false den #[]]
    rfl
  | .rad deg body, c => by
    show nodeChars c (radNode (listNodes disp #[] body)
        (listNodes false #[] deg)) = listChars (listChars c body) deg
    rw [radNode_chars, listNodes_chars disp body #[] c,
      listNodes_chars false deg #[]]
    rfl
  | .delim l r body, c => by
    cases l with
    | none =>
      cases r with
      | none =>
        show nodeListChars c (listNodes disp #[] body).toList = listChars c body
        rw [listNodes_chars disp body #[] c]
        rfl
      | some cr =>
        show nodeListChars c
            ((listNodes disp #[] body).push (delimMo cr)).toList
          = (listChars c body).push cr
        rw [Array.toList_push, nodeListChars_append,
          listNodes_chars disp body #[] c]
        show nodeChars (listChars c body) (delimMo cr) = _
        rw [delimMo_chars]
    | some cl =>
      cases r with
      | none =>
        show nodeListChars c (listNodes disp #[delimMo cl] body).toList
          = listChars (c.push cl) body
        rw [listNodes_chars disp body]
        show listChars (nodeChars c (delimMo cl)) body = _
        rw [delimMo_chars]
      | some cr =>
        show nodeListChars c
            ((listNodes disp #[delimMo cl] body).push (delimMo cr)).toList
          = (listChars (c.push cl) body).push cr
        rw [Array.toList_push, nodeListChars_append,
          listNodes_chars disp body]
        show nodeChars (listChars (nodeChars c (delimMo cl)) body)
            (delimMo cr) = _
        rw [delimMo_chars, delimMo_chars]
  | .accent mark stretch body, c => by
    cases h : mark == '\u0305' <;> simp only [nucNode, nucChars, h]
    · show nodeChars
          (nodeListChars c (listNodes disp #[] body).toList)
          (.elem "mo" #[("stretchy", if stretch then "true" else "false")]
            #[.text (charText mark)]) = _
      rw [listNodes_chars disp body #[] c, moLeaf_chars]
      rfl
    · show nodeChars
          (nodeListChars c (listNodes disp #[] body).toList)
          (.elem "mo" #[("stretchy", "true")]
            #[.text (charText overlineChar)]) = _
      rw [listNodes_chars disp body #[] c, moLeaf_chars]
      rfl
  | .grid kind rows, c => by
    cases kind <;>
      simp only [nucNode, nucChars] <;>
      show nodeListChars c (rowsNodes _ _ #[] rows).toList = rowsChars c rows <;>
      rw [rowsNodes_chars] <;>
      rfl

theorem rowNodes_chars (disp : Bool) (kind : GridKind) :
    ∀ (row : MRow) (k : Nat) (acc : Array Html.Node) (c : Array Char),
      nodeListChars c (rowNodes disp kind k acc row).toList
        = rowChars (nodeListChars c acc.toList) row
  | .nil, _, acc, c => rfl
  | .cons cell rest, k, acc, c => by
    show nodeListChars c (rowNodes disp kind (k + 1) _ rest).toList
        = rowChars (listChars (nodeListChars c acc.toList) cell) rest
    rw [rowNodes_chars disp kind rest, Array.toList_push,
      nodeListChars_append]
    simp only [nodeListChars]
    show rowChars (nodeListChars (nodeListChars c acc.toList)
        (listNodes disp #[] cell).toList) rest = _
    rw [listNodes_chars disp cell #[]]
    rfl

theorem rowsNodes_chars (disp : Bool) (kind : GridKind) :
    ∀ (rows : MRows) (acc : Array Html.Node) (c : Array Char),
      nodeListChars c (rowsNodes disp kind acc rows).toList
        = rowsChars (nodeListChars c acc.toList) rows
  | .nil, acc, c => rfl
  | .cons row rest, acc, c => by
    show nodeListChars c (rowsNodes disp kind _ rest).toList
        = rowsChars (rowChars (nodeListChars c acc.toList) row) rest
    rw [rowsNodes_chars disp kind rest, Array.toList_push,
      nodeListChars_append]
    simp only [nodeListChars]
    show rowsChars (nodeListChars (nodeListChars c acc.toList)
        (rowNodes disp kind 0 #[] row).toList) rest = _
    rw [rowNodes_chars disp kind row 0 #[]]
    rfl

end

/-- The MathML census: the emission's leaf text — the `mi`/`mn`/`mo`
contents in order, which is all the text the element carries — equals the
pure glyph-text fold over the same math list, for either display mode and
whatever backend attributes ride on the element. What this holds fixed:
the projection to MathML drops no glyph the AST carries and invents none
beyond it; the fold's agreement with the PDF's coverage census
(`Math.MList.scalarsList` — same scalars, its order, overline excepted)
is pinned by test in `mathmlChecks`. -/
theorem mathml_glyphs_agree (display : Bool) (extra : Array (String × String))
    (body : MList) :
    nodeChars #[] (formula display extra body) = listChars #[] body := by
  simp only [formula, nodeChars]
  rw [listNodes_chars display body #[] #[]]
  rfl

end LeanTex.Core.MathMl
