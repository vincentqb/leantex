import LeanTex.Core.Diag
import LeanTex.Core.Dim

namespace LeanTex.Core.Ir

open LeanTex.Core LeanTex.Core.Dim

/-- Page geometry, as declared by `\page`. -/
structure PageSpec where
  width : Sp := pt 612
  height : Sp := pt 792
  vmargin : Sp := inch 1
  hmargin : Sp := inch 1
  /-- Line spacing as a factor over the default 1.2, in thousandths, so
  `\linespread{1.04}` has a home. -/
  leading : Nat := 1000
  /-- The gap between peer paragraphs, with its rubber; `none` is the
  engine's default. LaTeX classes declare `0pt`, `\parskip` and the parskip
  package their own. -/
  parskip : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- An sRGB colour. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Repr, BEq, Inhabited

def Color.black : Color := { r := 0, g := 0, b := 0 }

/-- PDF wants components in 0–1; three decimals is finer than 8-bit input. -/
def Color.pdfComponents (c : Color) : String :=
  let f (v : UInt8) : String :=
    let milli := (v.toNat * 1000 + 127) / 255
    if milli == 0 then "0" else if milli == 1000 then "1"
    else
      let frac := toString milli
      let frac := ("".pushn '0' (3 - frac.length)) ++ frac
      "0." ++ (frac.dropEndWhile (· == '0')).toString
  s!"{f c.r} {f c.g} {f c.b}"

/-- Named lengths declared by `\tokens`, in declaration order so a later
token may be defined in terms of an earlier one. -/
structure Tokens where
  entries : Array (String × SymGlue) := #[]
  deriving Repr, BEq, Inhabited

def Tokens.find? (t : Tokens) (name : String) : Option SymGlue :=
  (t.entries.find? (·.1 == name)).map (·.2)

/-- Named colours declared by `\palette`. -/
structure Palette where
  entries : Array (String × Color) := #[]
  deriving Repr, BEq, Inhabited

def Palette.find? (p : Palette) (name : String) : Option Color :=
  (p.entries.find? (·.1 == name)).map (·.2)

/-- Font families a document asks for, as declared by `\fonts`. `dirs` are
directories of font files the document ships, relative to the document, so a
document that carries its fonts renders the same on every host. Every `dir`
declared is kept: fontspec's `Path=` may name a different one per face. -/
structure FontSpec where
  body : Option String := none
  sans : Option String := none
  mono : Option String := none
  dirs : Array String := #[]
  deriving Repr, BEq, Inhabited

/-- What to build, as declared by `\output`: the document carries its own
build intent, the way `\documentclass` already does. Names stay strings here
so the core does not know the CLI's option types. -/
structure OutputSpec where
  formats : Array String := #[]
  css : Option String := none
  deriving Repr, BEq, Inhabited

/-- PDF document information, as declared by `\pdfmeta`. -/
structure Meta where
  title : Option String := none
  author : Option String := none
  subject : Option String := none
  keywords : Option String := none
  deriving Repr, BEq, Inhabited

inductive CmpOp where
  | eq
  | ne
  | le
  | lt
  | ge
  | gt
  deriving Repr, BEq, Inhabited

def CmpOp.label : CmpOp → String
  | .eq => "=="
  | .ne => "!="
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

def CmpOp.holds : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b

/-- A layout invariant the engine checks against what it actually shipped. -/
inductive AssertKind where
  | pages (op : CmpOp) (n : Int)
  | fontsAllEmbedded
  deriving Repr, BEq, Inhabited

def AssertKind.source : AssertKind → String
  | .pages op n => s!"pages {op.label} {n}"
  | .fontsAllEmbedded => "fonts.all_embedded"

structure Assertion where
  kind : AssertKind
  span : Option Span := none
  deriving Repr, BEq, Inhabited

inductive Style where
  | bold
  | italic
  | mono
  | smallcaps
  | emph
  | sans
  | normal
  | size (name : String)
  deriving Repr, BEq

/-- The base font size every relative measure hangs off. It lives in the IR
because both backends read it: layout sets body text at this size, and HTML
derives its content measure from the page's text width in these units. -/
def baseFontSize : Sp := Dim.pt 10

/-- The LaTeX 10pt size scale, per mille of the surrounding size. It lives in
the IR because both backends read it: they must agree on what `\Huge` means. -/
def sizeScale : List (String × Nat) :=
  [("tiny", 500), ("scriptsize", 700), ("footnotesize", 800), ("small", 900),
   ("normalsize", 1000), ("large", 1200), ("Large", 1440), ("LARGE", 1728),
   ("huge", 2074), ("Huge", 2488)]

def Style.label : Style → String
  | .bold => "bold"
  | .italic => "italic"
  | .mono => "mono"
  | .smallcaps => "smallcaps"
  | .emph => "emph"
  | .sans => "sans"
  | .normal => "normal"
  | .size n => s!"size:{n}"

inductive Inline where
  | text (s : String)
  | math (display : Bool) (src : String)
  | styled (style : Style) (body : Array Inline)
  /-- `name` is the palette entry this came from, when it had one, so the
  HTML backend can emit `var(--name)` and let a host page override it. -/
  | colored (color : Color) (name : Option String) (body : Array Inline)
  /-- `\href{url}{body}`: a hyperlink. Becomes an `<a>` in HTML and a Link
  annotation in PDF, so the URL rides the IR rather than a backend. -/
  | link (url : String) (body : Array Inline)
  /-- `\underline{...}`: a drawn decoration, not a face change, so it is not a
  `Style`. Both backends interrupt the rule where a descender crosses it. -/
  | underline (body : Array Inline)
  /-- `\hfill`: stretch that pushes what follows to the far margin. -/
  | fill
  /-- Running-content placeholders, resolved once page count is known. -/
  | pageNumber
  | pageCount
  /-- `\\`, carrying LaTeX's optional extra space: `\\[1ex]`. -/
  | linebreak (extra : SymGlue)
  deriving Repr, BEq, Inhabited

inductive Block where
  | para (content : Array Inline)
  | section (level : Nat) (starred : Bool) (title : Array Inline)
  | list (ordered : Bool) (items : Array (Array Block))
  | center (body : Array Block)
  /-- `\block[before = <len>]{...}`: content with declared space above. -/
  | spaced (before : SymGlue) (body : Array Block)
  /-- `{verbatim}` content, kept literally: lines, spaces, and all. Both
  backends set it in the mono face and neither reflows it. -/
  | verbatim (content : String)
  deriving Repr, BEq, Inhabited

/-- Verbatim content, line-split: the newline after `\begin{verbatim}` and
the blank indentation before `\end{verbatim}` delimit; everything between is
content, interior blank lines included. -/
def verbatimLines (s : String) : Array String := Id.run do
  let s := if s.startsWith "\n" then (s.drop 1).toString
    else if s.startsWith "\r\n" then (s.drop 2).toString else s
  let mut lines := ((s.splitOn "\n").map fun l =>
    if l.endsWith "\r" then (l.dropEnd 1).toString else l).toArray
  if let some last := lines.back? then
    if last.trimAscii.isEmpty then lines := lines.pop
  return lines

/-- Verbatim content as inline text, for a backend that sets lines rather
than reading the string whole: spaces become no-break spaces so indentation
survives layout as fixed kerns, lines join by forced breaks, and a blank line
keeps one no-break space so the break before it still sets a line. -/
def verbatimInlines (s : String) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for line in verbatimLines s do
    unless out.isEmpty do
      out := out.push (.linebreak {})
    let kept := String.ofList (line.toList.map fun c => if c == ' ' then '\u00a0' else c)
    out := out.push (.text (if kept.isEmpty then "\u00a0" else kept))
  return out

/-- How an element kind looks, from `\style{element}{...}`. Every field a
backend used to hard-code is here instead, so a design lives in the document.
`font` is a template: the inline wrappers a declaration like
`{\large\sffamily\bfseries\primary}` elaborates to, with an empty body where
the element's own content goes. -/
structure ElementStyle where
  font : Option (Array Inline) := none
  before : Option SymGlue := none
  after : Option SymGlue := none
  /-- A rule filling the rest of the heading's line, in this palette colour. -/
  rule : Option (Color × Option String) := none
  /-- List marker content, replacing the default en dash. -/
  marker : Option (Array Inline) := none
  indent : Option SymGlue := none
  /-- Space between list items. -/
  gap : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- Elements a document may style. Section levels are `section`, `subsection`,
`subsubsection`; lists are `itemize` and `enumerate`. -/
def styleableElements : List String :=
  ["section", "subsection", "subsubsection", "itemize", "enumerate"]

structure Styles where
  entries : Array (String × ElementStyle) := #[]
  deriving Repr, BEq, Inhabited

def Styles.find? (s : Styles) (element : String) : Option ElementStyle :=
  (s.entries.find? (·.1 == element)).map (·.2)

mutual

def fillOne (content : Array Inline) : Inline → Inline
  | .styled st body =>
    .styled st (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .colored c n body =>
    .colored c n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .underline body =>
    .underline (if body.isEmpty then content else (fillList content body.toList).toArray)
  | other => other

def fillList (content : Array Inline) : List Inline → List Inline
  | [] => []
  | x :: rest => fillOne content x :: fillList content rest

end

/-- Fill a font template's hole with content. The hole is the innermost empty
body; a template with no hole (plain content) is returned unchanged, which
is what a marker is. -/
def fillTemplate (template content : Array Inline) : Array Inline :=
  if template.isEmpty then content else (fillList content template.toList).toArray

structure Doc where
  docClass : String := "article"
  classOptions : String := ""
  page : PageSpec := {}
  fonts : FontSpec := {}
  palette : Palette := {}
  tokens : Tokens := {}
  /-- `\runninghead` / `\runningfoot`: one line of inline content each, laid
  out in the margin after the body, when the page count is known. -/
  head : Option (Array Inline) := none
  foot : Option (Array Inline) := none
  /-- First page that carries running content; `\thispagestyle{empty}` on the
  opening page is `2`. -/
  runningFrom : Nat := 1
  styles : Styles := {}
  info : Meta := {}
  output : OutputSpec := {}
  asserts : Array Assertion := #[]
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

/-- Render a symbolic glue the way it was declared, so goldens show intent
rather than a resolved number. -/
def dumpGlue (g : SymGlue) : String :=
  let part (l : Length) : String :=
    let bits := (if l.sp != 0 then [s!"{l.sp.toPtString}pt"] else []) ++
      (if l.em != 0 then [s!"{l.em}/1000em"] else []) ++
      (if l.ex != 0 then [s!"{l.ex}/1000ex"] else [])
    if bits.isEmpty then "0" else String.intercalate "+" bits
  let base := part g.width
  let plus := if g.stretch == ({} : Length) then "" else s!" plus {part g.stretch}"
  let minus := if g.shrink == ({} : Length) then "" else s!" minus {part g.shrink}"
  base ++ plus ++ minus

private def hex2 (v : UInt8) : String :=
  let d := "0123456789ABCDEF".toList
  String.ofList [d[v.toNat / 16]!, d[v.toNat % 16]!]

-- Display-only printers. Structural recursion through `List`, so no `partial`.

mutual

/-- The characters of inline content with every mark stripped: what a URL or
a palette key built from a parameter is worth as text. -/
def plainText (xs : Array Inline) : String :=
  plainTextList xs.toList

def plainTextList (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => plainTextOne x ++ plainTextList rest

def plainTextOne (x : Inline) : String :=
  match x with
  | .text s => s
  | .math _ src => src
  | .styled _ body => plainTextList body.toList
  | .colored _ _ body => plainTextList body.toList
  | .link _ body => plainTextList body.toList
  | .underline body => plainTextList body.toList
  | .fill | .pageNumber | .pageCount => ""
  | .linebreak _ => " "

end

mutual

def dumpInlines (ind : String) (xs : Array Inline) : String :=
  dumpInlineList ind xs.toList

def dumpInlineList (ind : String) (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest

def dumpInline (ind : String) (x : Inline) : String :=
  match x with
  | .text s => s!"{ind}text {s.quote}\n"
  | .math d src =>
    let kind := if d then "display" else "inline"
    s!"{ind}math {kind} {src.quote}\n"
  | .styled st body => s!"{ind}styled {st.label}\n" ++ dumpInlines (ind ++ "  ") body
  | .colored c name body =>
    let tag := match name with
      | some n => s!"{n} #{hex2 c.r}{hex2 c.g}{hex2 c.b}"
      | none => s!"#{hex2 c.r}{hex2 c.g}{hex2 c.b}"
    s!"{ind}color {tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .link url body =>
    s!"{ind}link {url.quote}\n" ++ dumpInlines (ind ++ "  ") body
  | .underline body =>
    s!"{ind}underline\n" ++ dumpInlines (ind ++ "  ") body
  | .fill => s!"{ind}fill\n"
  | .pageNumber => s!"{ind}pagenumber\n"
  | .pageCount => s!"{ind}pagecount\n"
  | .linebreak extra =>
    if extra == ({} : SymGlue) then s!"{ind}linebreak\n"
    else s!"{ind}linebreak {dumpGlue extra}\n"

end

mutual

def dumpBlocks (ind : String) (xs : Array Block) : String :=
  dumpBlockList ind xs.toList

def dumpBlockList (ind : String) (xs : List Block) : String :=
  match xs with
  | [] => ""
  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest

def dumpItems (ind : String) (items : List (Array Block)) : String :=
  match items with
  | [] => ""
  | item :: rest =>
    s!"{ind}item\n" ++ dumpBlocks (ind ++ "  ") item ++ dumpItems ind rest

def dumpBlock (ind : String) (b : Block) : String :=
  match b with
  | .para content => s!"{ind}para\n" ++ dumpInlines (ind ++ "  ") content
  | .section level starred title =>
    let star := if starred then "*" else ""
    s!"{ind}section{star} {level}\n" ++ dumpInlines (ind ++ "  ") title
  | .list ordered items =>
    let kind := if ordered then "ordered" else "unordered"
    s!"{ind}list {kind}\n" ++ dumpItems (ind ++ "  ") items.toList
  | .center body => s!"{ind}center\n" ++ dumpBlocks (ind ++ "  ") body
  | .spaced before body =>
    s!"{ind}block before {dumpGlue before}\n" ++ dumpBlocks (ind ++ "  ") body
  | .verbatim s =>
    s!"{ind}verbatim\n" ++ String.join ((verbatimLines s).toList.map
      fun l => s!"{ind}  {l.quote}\n")

end

def dumpDiag (d : Diag) : String :=
  let where' := match d.span with
    | some sp => s!"{sp.pos.line}:{sp.pos.col}"
    | none => "-"
  let help := match d.help with
    | some h => s!" | help: {h}"
    | none => ""
  s!"{d.severity.label}[{d.code}] {where'} {d.message}{help}\n"

def dump (doc : Doc) (diags : Array Diag) : String :=
  let opts := if doc.classOptions == "" then "" else s!" [{doc.classOptions}]"
  let head := s!"class {doc.docClass}{opts}\n"
  let page :=
    s!"page {doc.page.width.toPtString}x{doc.page.height.toPtString} " ++
    s!"vmargin {doc.page.vmargin.toPtString} hmargin {doc.page.hmargin.toPtString}" ++
    (match doc.page.parskip with
      | some g => s!" parskip {dumpGlue g}"
      | none => "") ++ "\n"
  let metaLine (label : String) (v : Option String) : String :=
    match v with
    | some s => s!"meta {label} {s.quote}\n"
    | none => ""
  let fontLine (label : String) (v : Option String) : String :=
    match v with
    | some f => s!"font {label} {f.quote}
"
    | none => ""
  let fontLines :=
    String.join (doc.fonts.dirs.toList.map fun d => fontLine "dir" (some d)) ++
    fontLine "body" doc.fonts.body ++ fontLine "sans" doc.fonts.sans ++
    fontLine "mono" doc.fonts.mono
  let paletteLines := String.join (doc.palette.entries.toList.map fun (n, c) =>
    s!"palette {n} #{hex2 c.r}{hex2 c.g}{hex2 c.b}\n")
  let tokenLines := String.join (doc.tokens.entries.toList.map fun (n, g) =>
    s!"token {n} {dumpGlue g}\n")
  let runLines :=
    (match doc.head with
     | some xs => "runninghead\n" ++ dumpInlines "  " xs
     | none => "") ++
    (match doc.foot with
     | some xs => "runningfoot\n" ++ dumpInlines "  " xs
     | none => "")
  let infoLines :=
    metaLine "title" doc.info.title ++ metaLine "author" doc.info.author ++
    metaLine "subject" doc.info.subject ++ metaLine "keywords" doc.info.keywords
  let asserts := String.join (doc.asserts.toList.map fun a =>
    s!"assert {a.kind.source}\n")
  let body := dumpBlocks "" doc.body
  let ds :=
    if diags.isEmpty then
      "-- diagnostics\n(none)\n"
    else
      "-- diagnostics\n" ++ String.join (diags.toList.map dumpDiag)
  head ++ page ++ fontLines ++ paletteLines ++ tokenLines ++ runLines ++ infoLines ++ asserts ++ body ++ ds

end LeanTex.Core.Ir
