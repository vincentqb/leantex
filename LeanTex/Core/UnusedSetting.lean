module

public import LeanTex.Core.Ir
import Std.Data.HashMap
import Std.Data.HashSet

/-! The settings a document declares that nothing it sets uses: a colour no paint reads, a face no
text is set in, a style for an element the document never shows. -/

namespace LeanTex.Core.UnusedSetting

open LeanTex.Core Ir

/-- What a declaration configures, named by the content that alone reads it. -/
public inductive Setting where
  /-- An author colour, read by any paint or declaration naming it. -/
  | color (name : String)
  /-- A `\fonts` face (`body`, `sans`, `mono`, `math`, `family.<cmd>`), read by text set in it. -/
  | face (key : String)
  /-- A styleable element, read by that element where the document sets it. -/
  | style (element : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A setting at the site the document declares it. -/
public structure Declared where
  setting : Setting
  span : Span
  deriving Repr, BEq

/-- The written controls that load a package, class or theme, whose declarations are its own. -/
public def loaders : List String :=
  ["\\usepackage", "\\RequirePackage", "\\documentclass", "\\LoadClass", "\\usetheme",
   "\\usecolortheme", "\\usefonttheme", "\\useinnertheme", "\\useoutertheme", "\\theme"]

/-- The written controls that define a macro, whose lowering is the definition's. -/
public def definers : List String :=
  ["\\def", "\\gdef", "\\edef", "\\xdef", "\\let", "\\newcommand", "\\renewcommand",
   "\\providecommand", "\\DeclareRobustCommand"]

/-- Whether a declaration at `pos` is the document's own: outside a package or class file, a file
one inputs and any definition's replacement text, and loading or defining nothing. -/
public def ownSite (package inCall : Bool) (pos : Pos) : Bool :=
  !package && !inCall && pos.origins.isEmpty &&
    !(pos.command.any fun c => loaders.contains c || definers.contains c)

/-- A site's identity, as a diagnostic's span compares it. -/
private def siteKey (span : Span) : String × Nat × Nat := (span.file, span.pos.line, span.pos.col)

/-- What the document's content reads: the style elements it sets and the faces its text sets
in. -/
public structure Shown where
  elements : Array String := #[]
  faces : Array String := #[]
  /-- An image stands somewhere, whose words a later reader may set in the document's faces. -/
  images : Bool := false
  /-- A heading stands somewhere, which the web page sets in the sans family. -/
  headings : Bool := false
  deriving Repr, Inhabited

private def Shown.element (s : Shown) (el : String) : Shown :=
  if s.elements.contains el then s else { s with elements := s.elements.push el }

private def Shown.face (s : Shown) (k : String) : Shown :=
  if s.faces.contains k then s else { s with faces := s.faces.push k }

/-- The element a list at its kind's nesting depth reads beside its kind's own, as LaTeX's four
levels name them. -/
private def listLevel (kind : String) (depth : Nat) : Option String :=
  let level := min depth 4
  if level ≤ 1 then none else some s!"{kind}{level}"

/-- The faces and elements one inline node reads. -/
private def inlineReads (acc : Shown) : Inline → Shown
  | .styled .mono _ => acc.face "mono"
  | .styled .sans _ => acc.face "sans"
  | .styled .roman _ => acc.face "body"
  | .styled (.family s) _ => acc.face s!"family:{s}"
  | .formula _ _ _ | .math _ _ => acc.face "math"
  | .image _ _ _ => { acc with images := true }
  | .ref _ _ _ _ => acc.element "link"
  | .link _ _ => (acc.element "link").element "url"
  | .cite _ _ | .cited _ _ _ => acc.element "cite"
  | .role name _ => acc.element name
  | .footnote _ _ => acc.element "enumerate"
  | .styled _ _ | .colored _ _ _ | .located _ _ | .decorated _ _ | .onSteps _ _
  | .altSteps _ _ _ | .text _ | .icon _ _ | .label _ | .fill
  | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ => acc

/-- The inline walk, carrying the lists' nesting depths through. -/
private def inlineFold : CtxFold (Nat × Nat) Shown where
  openBlock := fun ctx acc _ => (acc, ctx)
  closeBlock := fun _ acc _ => acc
  openInline := fun ctx acc x => (inlineReads acc x, ctx)
  closeInline := fun _ acc _ => acc

/-- The elements one block reads on entry, every element of a tag the web page's rules address
counted, and the list depths its content stands at. -/
private def blockReads (ctx : Nat × Nat) (acc : Shown) (b : Block) : Shown × (Nat × Nat) :=
  let inlines (acc : Shown) (xs : Array Inline) : Shown := foldCtxInlines inlineFold ctx acc xs
  match b with
  | .section level _ _ _ =>
    let acc := { acc.element level.element with headings := true }
    (if level == .h2 then acc.element "sectionpage" else acc, ctx)
  | .abstract _ => ({ (acc.element "abstract").element "section" with headings := true }, ctx)
  | .algorithm _ _ _ =>
    (["enumerate", "enumerate2", "enumerate3", "enumerate4"].foldl Shown.element acc, ctx)
  | .bibliography _ _ _ => (acc.element "itemize", ctx)
  | .list ordered _ _ =>
    let kind := if ordered then "enumerate" else "itemize"
    let depth := (if ordered then ctx.2 else ctx.1) + 1
    let acc := acc.element kind
    -- An unordered list may be a description list, whose scopes it reads too.
    let kinds := if ordered then [(kind, depth)]
      else (kind, depth) :: [1, 2, 3, 4].map ("description", ·)
    let acc := kinds.foldl (fun acc (k, kd) =>
      (Ir.listSetScopes k (ctx.1 + ctx.2 + 1) kd).foldl Shown.element acc) acc
    let acc := match listLevel kind depth with
      | some el => acc.element el
      | none => acc
    (acc, if ordered then (ctx.1, depth) else (depth, ctx.2))
  | .frame title standout _ _ _ =>
    let acc := if standout then acc.element "standout" else acc
    (if title.isEmpty then acc
     else { (acc.element "frametitle").element "section" with headings := true }, ctx)
  | .titled kind _ _ =>
    ((kind.styleElement.map fun el => (acc.element el).element "block").getD acc, ctx)
  | .nav _ _ => (acc.element "nav", ctx)
  | .logo content => (if content.isEmpty then acc else acc.element "logo", ctx)
  | .role name _ => (acc.element name, ctx)
  | .equation _ _ => (acc.face "math", ctx)
  | .verbatim _ _ spec =>
    let acc := acc.face "mono"
    ((spec.caption.map fun (_, c) => inlines acc c).getD acc, ctx)
  | .picture pic => (pic.labelContents.foldl inlines acc, ctx)
  | .para _ | .center _ | .ragged _ _ | .spaced _ _ | .link _ _ | .quote _
  | .disclosure _ _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _
  | .note _ | .only _ _ | .pagebreak | .framefoot _ | .setPalette _ | .setTokens _
  | .rule _ _ _ | .table _ _ _ _ _ _ | .float _ _ _ _ _ => (acc, ctx)

/-- The block walk, each block read on entry. -/
private def blockFold : CtxFold (Nat × Nat) Shown :=
  { inlineFold with openBlock := blockReads }

/-- The text faces a drawing the engine reads later may set its words in: an image's, which an
SVG sets in the document's faces, and a picture the boundary tool draws. -/
private def drawnFaces : List String := ["body", "sans", "mono", "math"]

/-- What a document's body and furniture read, beside the elements the elaborator read as it set
them: a formula's text alphabet reads its text face, and an image or a boundary picture every
face. -/
-- conserves: none — reads what the content sets.
public def shown (doc : Doc) (consumed : Array String := #[]) : Shown :=
  let body := foldCtxBlocks blockFold (0, 0) { elements := consumed } doc.body
  let acc := (furnitureInlines doc).foldl (foldCtxInlines inlineFold (0, 0)) body
  let acc := if doc.headline.isSome then { acc.element "titlepage" with headings := true } else acc
  let acc := if doc.logo.isSome || doc.logoLeft.isSome || doc.logoRight.isSome then
    acc.element "logo" else acc
  let requests := mathRequests .alphabets doc
  let acc := if requests.isEmpty then acc else acc.face "math"
  let acc := [(Math.MathTextSlot.body, "body"), (.sans, "sans"), (.mono, "mono")].foldl
    (fun acc (slot, key) =>
      if requests.any (·.body.setsText slot doc.fonts.mathSources) then acc.face key else acc) acc
  if acc.images || !doc.pictureSrcs.isEmpty then drawnFaces.foldl Shown.face acc
  else acc

/-- Whether a face's declared family sets some text, through the slots it resolves, the math
companion it picks, or the web page's sans headings. -/
public def faceUsed (fonts : FontSpec) (slides : Bool) (shown : Shown) (key : String) : Bool :=
  let sets (k : String) := shown.faces.contains k
  match key with
  | "mono" => sets "mono"
  | "math" => sets "math"
  | "sans" => sets "sans" || slides || fonts.body.isNone || shown.headings
  | "body" =>
    !(slides && fonts.sans.isSome) || sets "body" || (sets "mono" && fonts.mono.isNone) ||
      (sets "math" && fonts.math.isNone)
  | k =>
    match (k.drop "family.".length).toString, k.startsWith "family." with
    | name, true => match fonts.familySlot name with
      | some slot => sets s!"family:{slot}"
      | none => true
    | _, false => true

/-- An element as the document sets it, in the plural. -/
private def elementNoun (el : String) : String :=
  (styleableNouns.lookup el).getD s!"uses of '\\{el}'"

/-- The nouns a site's elements name, in order and once each, joined as a list in prose. -/
private def nounsOf (elements : Array String) : String :=
  let nouns := elements.foldl (fun acc el =>
    let n := elementNoun el
    if acc.contains n then acc else acc.push n) #[]
  match nouns.toList.reverse with
  | [] => ""
  | [n] => n
  | last :: rest => String.intercalate ", " rest.reverse ++ " or " ++ last

/-- What the author can do about a declaration nothing reads: delete `what`, or accept it. -/
public def unusedHelp (what : String) : String := s!"delete {what}, or \\allow\{W0449} keeps it"

/-- The words and subject of listing defaults no listing after them reads, by the command that
declares them and its lexer layer. -/
public def listingWords (reader : String) (lang : Option String) : String × String :=
  let (what, which) := match reader, lang with
    | "lstset", _ => ("listing defaults", "no listing")
    | "setminted", none => ("minted defaults", "no minted listing")
    | "setminted", some l => (s!"minted defaults for '{l}'", s!"no minted '{l}' listing")
    | _, none => ("inline-code defaults", "no inline code")
    | _, some l => (s!"inline-code defaults for '{l}'", s!"no inline '{l}' code")
  (s!"{what} are declared here, and {which} after them reads them",
   s!"unused:listing:{reader}" ++ (lang.map (":" ++ ·)).getD "")

/-- The loss of a face the document declares that no text is set in. -/
public def faceDiag (key : String) (span : Span) : Diag :=
  if key == "math" then
    Diag.of .W0449 "the 'math' face is declared here, and the document sets no mathematics"
      (span := some span) (subject := some "unused:face:math")
      (help := some (unusedHelp "the 'math' face's entry"))
  else if key.startsWith "family." then
    let cmd := s!"'\\{(key.drop "family.".length).toString}'"
    Diag.of .W0449 s!"{cmd} declares a face here, and no text the document sets is set in it"
      (span := some span) (subject := some s!"unused:face:{key}")
      (help := some (unusedHelp s!"{cmd}'s declaration"))
  else
    Diag.of .W0449 s!"the '{key}' face is declared here, and no text the document sets is set in it"
      (span := some span) (subject := some s!"unused:face:{key}")
      (help := some (unusedHelp s!"the '{key}' face's entry"))

/-- The loss of a markdown metadata key only a citation reads, in a document citing nothing. -/
public def metaDiag (file key : String) (pos : Pos) : Diag :=
  Diag.of .W0449 s!"the metadata key '{key}' is declared here, and the document cites nothing"
    (span := some ⟨file, pos⟩) (subject := some s!"unused:meta:{key}")
    (help := some "cite an entry, as '[@key]' does, or delete the key")

/-- The loss of a Lean page's directive key only a citation reads, on a page whose documentation
cites nothing. -/
public def directiveDiag (file key : String) (pos : Pos) : Diag :=
  Diag.of .W0449 s!"the directive key '{key}' is declared here, and the page's documentation \
cites nothing"
    (span := some ⟨file, pos⟩) (subject := some s!"unused:directive:{key}")
    (help := some "cite an entry, as `[Key]` does, or delete the key")

/-- The loss of an author colour nothing paints with. -/
private def colorDiag (name : String) (span : Span) : Diag :=
  Diag.of .W0449 s!"the colour '{name}' is declared here, and nothing the document sets paints with it"
    (span := some span) (subject := some s!"unused:color:{name}")
    (help := some (unusedHelp s!"the declaration of '{name}'"))

/-- The loss of a site's styles for elements the document never sets. -/
private def styleDiag (elements : Array String) (span : Span) : Diag :=
  Diag.of .W0449 s!"this styles {nounsOf elements}, and the document sets none"
    (span := some span) (subject := some s!"unused:style:{",".intercalate elements.toList}")
    (help := some (unusedHelp "what it declares for them"))

/-- The losses of the colours nothing reads, one per site and colour, then of the style sites, each
in the order declared; the style elements one site declares are one setting, read when any is, and a
site another warning already names keeps that one accounting. -/
public def diags (ledger : Array Declared) (shown : Shown) (read : Std.HashSet String)
    (named : Array Span) : Array Diag := Id.run do
  let taken : Std.HashSet (String × Nat × Nat) := named.foldl (·.insert <| siteKey ·) {}
  let mut out : Array Diag := #[]
  let mut colors : Std.HashSet (String × String × Nat × Nat) := {}
  let mut sites : Array Span := #[]
  let mut styled : Std.HashMap (String × Nat × Nat) (Array String) := {}
  for d in ledger do
    let k := siteKey d.span
    if taken.contains k then continue
    match d.setting with
    | .color name =>
      unless read.contains name || colors.contains (name, k) do
        colors := colors.insert (name, k)
        out := out.push (colorDiag name d.span)
    | .style el =>
      match styled[k]? with
      | some els => unless els.contains el do styled := styled.insert k (els.push el)
      | none =>
        styled := styled.insert k #[el]
        sites := sites.push d.span
    | .face _ => pure ()
  for span in sites do
    let els := styled[siteKey span]?.getD #[]
    unless els.any shown.elements.contains do out := out.push (styleDiag els span)
  return out

/-- The faces the document declares, once per face and site no other warning names, which the face
set's judge reads. -/
public def faceSites (ledger : Array Declared) (named : Array Span) : Array (String × Span) :=
  let taken : Std.HashSet (String × Nat × Nat) := named.foldl (·.insert <| siteKey ·) {}
  (ledger.foldl (init := (#[], (∅ : Std.HashSet (String × String × Nat × Nat))))
    fun (out, seen) d => match d.setting with
      | .face key =>
        let k := siteKey d.span
        if taken.contains k || seen.contains (key, k) then (out, seen)
        else (out.push (key, d.span), seen.insert (key, k))
      | .color _ | .style _ => (out, seen)).1

end LeanTex.Core.UnusedSetting
