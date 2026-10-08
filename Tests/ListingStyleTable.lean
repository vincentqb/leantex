import Tests.ListingProvider

open LeanTex.Core

/-! Listing token paint against Pygments' own answers. The oracle
(`testdata/oracles/pygments-styles.tsv`, regenerated with
`scripts/gen-pygments-style-data.lean`) holds, for every standard token type
of every shipped style, `style_for_token` and what the LaTeX formatter minted
runs ships; the artifacts are then held to the engine's reading of it. -/

namespace Tests.ListingStyleTable

open LeanTex.Core.ListingHighlight (Kind Token)
open LeanTex.Core.PygmentsStyle (Box)

def oraclePath : String := "testdata/oracles/pygments-styles.tsv"

/-- The oracle's rows as cells; provenance and the header are not rows. -/
def oracleRows : IO (Array (Array String)) := do
  let text ← IO.FS.readFile oraclePath
  return ((text.splitOn "\n").filter fun l =>
    !l.isEmpty && !l.startsWith "#" && !l.startsWith "style\t").toArray.map
      fun l => (l.splitOn "\t").toArray

/-- A channel as the LaTeX formatter writes it, `'%.2f' % (v / 255)`: no
8-bit channel lies on a tie, so rounding to nearest is the whole rule. -/
def twoDp (v : UInt8) : String :=
  let n := (200 * v.toNat + 255) / 510
  s!"{n / 100}.{if n % 100 < 10 then "0" else ""}{n % 100}"

def texRgb (c : Ir.Color) : String := s!"{twoDp c.r},{twoDp c.g},{twoDp c.b}"

def hexCell : Option Ir.Color → String
  | some c => Ir.Color.hexByte c.r ++ Ir.Color.hexByte c.g ++ Ir.Color.hexByte c.b
  | none => "-"

def bit (b : Bool) : String := if b then "1" else "0"

def boxCell : Option Box → String
  | none => "-"
  | some (.frame border fill) =>
    s!"frame:{texRgb border}/{if fill == Ir.Color.white then "1,1,1" else texRgb fill}"
  | some (.fill fill) => s!"fill:{texRgb fill}"

/-- The engine's two readings of one type, in the oracle's spelling: Pygments'
inheritance, then the LaTeX formatter's composition. The chain cell is
Pygments' own spelling, passed through. -/
def cellsOf (style : Ir.ListingStyle) (type chain : String) : Array String :=
  let table := Listing.table style
  let k := Kind.ofPygments type
  let r := table.resolvedOf k
  let l := table.lookOf k
  #[style.name, type, hexCell (r.color.map (·.1)), bit r.bold, bit r.italic, bit r.underline,
    hexCell r.bgcolor, hexCell r.border, chain, (l.color.map (texRgb ·.1)).getD "-",
    bit l.bold, bit l.italic, bit l.underline, boxCell l.box]

/-- `ink` is `seed` where `seed` is legible on `ground`, and otherwise the
least whole-percent xcolor mix of `seed` toward a pole that is: the bounded
adjustment, read off the result rather than restating its search. -/
def leastLegible (ground seed ink : Ir.Color) : Bool :=
  let ok (c : Ir.Color) := Contrast.contrastMilli c ground ≥ Contrast.aaText
  if ok seed then ink == seed
  else ok ink && [Ir.Color.black, Ir.Color.white].any fun pole =>
    match (List.range 100).find? (fun i => seed.mix (100 - (i + 1)) pole == ink) with
    | some i => (List.range i).all fun j => !ok (seed.mix (100 - (j + 1)) pole)
    | none => false

/-- What a weight is in the four-face set: regular 0, bold 1, italic 2,
bold italic 3 (`serifFacesSet`). -/
def faceOf (bold italic : Bool) : Nat := (if bold then 1 else 0) + (if italic then 2 else 0)

/-- Each shipped line's runs: face index, colour and glyphs. -/
def linePaint (l : Layout.LineOut) : Array (Nat × Ir.Color × String) :=
  l.segs.foldl (fun acc seg => match seg with
    | .run idx color _ _ glyphs _ _ _ _ _ _ =>
      acc.push (idx, color, String.ofList (glyphs.map (·.2.1)).toList)
    | _ => acc) #[]

/-- Every glyph's character, face index and colour, in page order. -/
def glyphPaint (out : Layout.Out) : Array (Char × Nat × Ir.Color) :=
  (bodyLines out).foldl (fun acc l => (linePaint l).foldl (fun acc (idx, color, text) =>
    text.toList.foldl (fun acc c => acc.push (c, idx, color)) acc) acc) #[]

/-- A character's paint in the typed HTML: the innermost `color` declaration
over it, and whether it sits inside `strong`, `em` and `u`. -/
structure HtmlPaint where
  color : Option String := none
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  deriving Inhabited, BEq

mutual

def htmlPaintOne (cur : HtmlPaint) (acc : Array (Char × HtmlPaint)) :
    Html.Node → Array (Char × HtmlPaint)
  | .text text => text.toList.foldl (fun acc c => acc.push (c, cur)) acc
  | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    let color := (attrs.find? fun (key, value) =>
      tag == "span" && key == "style" && hasStr value "color:").map (·.2)
    let cur := { cur with
      color := color.or cur.color
      bold := cur.bold || tag == "strong"
      italic := cur.italic || tag == "em"
      underline := cur.underline || tag == "u" }
    htmlPaintList cur acc kids.toList

def htmlPaintList (cur : HtmlPaint) (acc : Array (Char × HtmlPaint)) :
    List Html.Node → Array (Char × HtmlPaint)
  | [] => acc
  | n :: ns => htmlPaintList cur (htmlPaintOne cur acc n) ns

end

/-- The paint of the listing's code, line by line. -/
def htmlLines (doc : Ir.Doc) : Array (Array (Char × HtmlPaint)) :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let codes := ListingHighlight.codeNodesList #[] body.toList
  let chars := htmlPaintList {} #[] codes.toList
  chars.foldl (fun lines (c, p) =>
    if c == '\n' then lines.push #[] else lines.modify (lines.size - 1) (·.push (c, p))) #[#[]]

/-- A document holding one listing whose every line is one token of one type. -/
def typeDoc (style : Ir.ListingStyle) (kinds : Array Kind) : Ir.Doc :=
  let lines := kinds.mapIdx fun i _ => s!"ab{i}"
  let source := String.intercalate "\n" lines.toList
  let highlight := (kinds.zip lines).map fun (kind, text) => #[({ kind, text } : Token)]
  { (elabStr (dvDoc "" "")).1 with
    body := #[.verbatim none source { style, highlight }] }

/-- A real Lean listing with proof holes, through minted's surface. -/
def holeSource : String := "theorem t : True := by\n  sorry\nexample : True := by admit"

def holeDoc (style : Ir.ListingStyle) : Ir.Doc × Array Diag :=
  elabStr (dvDoc ("\\usepackage{minted}\\setminted{style=" ++ style.name ++ "}")
    ("\\begin{minted}{lean4}\n" ++ holeSource ++ "\n\\end{minted}"))

/-- A provider listing whose classes carry boxes in the shipped styles. -/
def boxedAnswer : ListingReply.Answer :=
  { request := ListingReply.Request.ofSource "bash" "x$y"
    tokens := #[#[{ kind := Kind.ofPygments "Token.Name", text := "x" },
      { kind := Kind.ofPygments "Token.Error", text := "$" },
      { kind := Kind.ofPygments "Token.Comment.Special", text := "y" }]] }

def boxedDoc (style : Ir.ListingStyle) (copies : Nat) : Ir.Doc × Array Diag :=
  let listing := "\\begin{minted}{bash}\nx$y\n\\end{minted}\n"
  let (base, earlier) := ListingProvider.prepared false
    (dvDoc ("\\usepackage{minted}\\setminted{style=" ++ style.name ++ "}")
      (String.join (List.replicate copies listing)))
  let (doc, ds, _) := Elab.runPrepared "listing"
    { base with listingReplies := #[boxedAnswer] } earlier
  (doc, ds)

end Tests.ListingStyleTable

namespace Tests

open Tests.ListingStyleTable
open LeanTex.Core.ListingHighlight (Kind)

/-- **Every token type of every shipped style is painted as Pygments and
minted paint it, in both artifacts.** The engine's resolution of the
generated declarations equals `style_for_token`, and its composition equals
what minted's `\PYG` chain ships (a `nobold` under a bold type stays bold, as
a lualatex build shows); a style colour ships unchanged where legible and
otherwise as the least legible mix; PDF glyphs and typed HTML carry each
type's ink and weights. On the base tree the painter knew seven classes:
`Generic.Error` and the other types fell to plain, and a proof hole shipped
in bold keyword green. -/
def listingStyleTableChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let rows ← oracleRows
  t "pygments styles: every shipped declaration parses" PygmentsStyle.declarationsParse
  let typesOf (style : Ir.ListingStyle) : Array String :=
    (rows.filter (·[0]? == some style.name)).map (·.getD 1 "")
  t "pygments styles: the oracle names exactly the shipped styles"
    (rows.all fun r => Ir.ListingStyle.all.any (some ·.name == r[0]?))
  let types := typesOf .default
  t "pygments styles: every shipped style has one row per standard type"
    (!types.isEmpty && types.toList.eraseDups.length == types.size &&
      Ir.ListingStyle.all.all fun s => typesOf s == types)
  for row in rows do
    let some style := Ir.ListingStyle.ofName? (row.getD 0 "") | continue
    let type := row.getD 1 ""
    let chain := row.getD 8 ""
    let got := cellsOf style type chain
    t s!"pygments styles: {style.name} {type} resolves as style_for_token and composes as minted ships it (engine {got}, Pygments {row})"
      (got == row)
    t s!"pygments styles: {style.name} {type} applies one style per level of its chain"
      (chain == "-" || (chain.splitOn "+").length == (Kind.ofPygments type).chain.length)
    for ground in [Ir.Color.white, Ir.Color.black] do
      let k := Kind.ofPygments type
      let look := (Listing.table style).lookOf k
      t s!"pygments styles: {style.name} {type} ships its colour, or the least legible mix of it, on {ground.css}"
        (match look.color, Listing.ink {} (some ground) k (style := style) with
          | some (seed, _), some ink => leastLegible ground seed ink
          | none, none => true
          | _, _ => false)
  let some fonts ← serifFacesSet | failures ref "pygments styles: the serif faces load"
  let kinds := types.map Kind.ofPygments
  for style in Ir.ListingStyle.all do
    let doc := typeDoc style kinds
    let fg := (Ir.Design.ofDoc doc).fg
    let lines := (bodyLines (layoutOf fonts doc)).filter fun l => !(linePaint l).isEmpty
    let html := htmlLines doc
    t s!"pygments styles: {style.name} ships one line per type in both artifacts"
      (lines.size == kinds.size && html.size == kinds.size)
    for ((k, line), chars) in (kinds.zip lines).zip html do
      let look := (Listing.table style).lookOf k
      let ink := Listing.ink doc.palette none k (style := style)
      t s!"pygments styles: {style.name} {k.path} PDF glyphs carry its ink and weight"
        ((linePaint line).all fun (idx, color, _) =>
          color == ink.getD fg && idx == faceOf look.bold look.italic)
      t s!"pygments styles: {style.name} {k.path} typed HTML carries its ink and weight"
        (!chars.isEmpty && chars.all fun (_, p) =>
          p.bold == look.bold && p.italic == look.italic && p.underline == look.underline &&
          match ink with
          | some c => p.color.any (hasStr · (HtmlDoc.cssColor c))
          | none => p.color.isNone)
  -- The report: a Lean proof hole under minted's styles.
  let friendlyRed := Listing.ink {} none .genericError (style := .friendly)
  t "pygments styles: friendly's Generic.Error red is legible and barely different from #FF0000"
    (friendlyRed.any fun c => c != Ir.Color.ofHtml 255 0 0 &&
      Contrast.contrastMilli c Ir.Color.white ≥ Contrast.aaText &&
      Contrast.withinInkBound (Ir.Color.ofHtml 255 0 0) c)
  t "pygments styles: default's Generic.Error ships its own #E40000"
    (Listing.ink {} none .genericError (style := .default) == some (Ir.Color.ofHtml 228 0 0))
  for style in Ir.ListingStyle.all do
    let (doc, ds) := holeDoc style
    t s!"listing holes {style.name}: the minted listing elaborates clean"
      (ds.all (·.severity != .error))
    let fg := (Ir.Design.ofDoc doc).fg
    let some red := Listing.ink doc.palette none .genericError (style := style)
      | failures ref s!"listing holes {style.name}: the style gives Generic.Error no ink"
    let some green := Listing.ink doc.palette none .keyword (style := style)
      | failures ref s!"listing holes {style.name}: the style gives Keyword no ink"
    t s!"listing holes {style.name}: the error ink is neither the text's nor the keywords'"
      (red != fg && red != green)
    let glyphs := (glyphPaint (layoutOf fonts doc)).filter fun (c, _) => ShellHighlight.visible c
    let laid := glyphs.map fun (c, idx, color) => (c, (idx, color))
    let typedChars := (htmlLines doc).flatten.filter fun (c, _) => ShellHighlight.visible c
    for hole in ["sorry", "admit"] do
      t s!"listing holes {style.name}: PDF sets {hole} in the error red, regular weight"
        ((ShellHighlight.witnessPaint? holeSource hole laid).any fun paint =>
          !paint.isEmpty && paint.all (· == (0, red)))
      let typed := ShellHighlight.witnessPaint? holeSource hole typedChars
      t s!"listing holes {style.name}: typed HTML sets {hole} in the error red, not strong"
        (typed.any fun paint => !paint.isEmpty && paint.all fun p =>
          !p.bold && p.color.any (hasStr · (HtmlDoc.cssColor red)))
    t s!"listing holes {style.name}: the keyword beside the hole keeps bold keyword ink"
      ((ShellHighlight.witnessPaint? holeSource "theorem" laid).any fun paint =>
        !paint.isEmpty && paint.all (· == (1, green)))
  -- A box the inlines cannot carry is named, keyed by its type, and the
  -- token's text and colour still ship.
  for (style, subjects) in [(Ir.ListingStyle.default, ["listing-token:Error"]),
      (.friendly, ["listing-token:Error", "listing-token:Comment.Special"])] do
    let (doc, ds) := boxedDoc style 2
    let named := ds.filter (·.code == "W0397")
    t s!"listing boxes {style.name}: W0397 names each boxed type at each site"
      (named.size == 2 * subjects.length &&
        subjects.all fun s => (named.filter (·.subject == some s)).size == 2)
    t s!"listing boxes {style.name}: no other loss is reported"
      (ds.all fun d => d.code == "W0397" || d.severity != .warning)
    let glyphs := glyphPaint (layoutOf fonts doc)
    t s!"listing boxes {style.name}: both artifacts keep the boxed tokens' text"
      (String.ofList (glyphs.toList.map (·.1)) == "x$yx$y" &&
        (htmlLines doc).flatten.map (·.1) == "x$yx$y".toList.toArray)
    let special := Listing.ink doc.palette none (Kind.ofPygments "Token.Comment.Special")
      (style := style)
    t s!"listing boxes {style.name}: a boxed token keeps its own ink"
      (special.isSome && glyphs.all fun (c, _, color) => c != 'y' || some color == special)

end Tests
