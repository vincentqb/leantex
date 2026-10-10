module

public import Tests.ListingProvider

public section

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
  let table := CodeColor.table style
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
      t s!"code roles: {style.name} {type} ships its role's style colour, or the least legible mix of it, on {ground.css}"
        (match CodeColor.styleColor style k.role, Listing.ink {} (some ground) k (style := style) with
          | some seed, some ink => leastLegible ground seed ink
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
      let (bold, italic) := k.role.weights
      let ink := Listing.ink doc.palette none k (style := style)
      t s!"code roles: {style.name} {k.path} PDF glyphs carry its role's ink and weight"
        ((linePaint line).all fun (idx, color, _) =>
          color == ink.getD fg && idx == faceOf bold italic)
      t s!"code roles: {style.name} {k.path} typed HTML carries its role's ink and weight"
        (!chars.isEmpty && chars.all fun (_, p) =>
          p.bold == bold && p.italic == italic && !p.underline &&
          match ink with
          | some c => p.color.any (hasStr · (HtmlDoc.cssColor c))
          | none => p.color.isNone)
    for r in ListingHighlight.Role.all do
      let inks := (kinds.filter (·.role == r)).map fun k => Listing.ink doc.palette none k (style := style)
      t s!"code roles: {style.name} every type of the {repr r} role ships one ink"
        (inks.all (· == inks[0]?.getD none))
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

/-- Two languages' must-not-ship markers: a Lean proof hole and a raised
not-implemented error, one minted listing each, under an invented palette. -/
def markerLean : String := "theorem t : True := by\n  sorry"
def markerPython : String := "def f():\n    raise NotImplementedError"

def markerDoc (preamble : String) : Ir.Doc × Array Diag :=
  elabStr (dvDoc ("\\usepackage{minted}" ++ preamble)
    ("\\begin{minted}{lean4}\n" ++ markerLean ++ "\n\\end{minted}\n" ++
     "\\begin{minted}{python}\n" ++ markerPython ++ "\n\\end{minted}"))

/-- Oklab hue geometry over shipped colours, for the derivation checks: the
cosine of the hue angle between two colours, in thousandths, and a colour's
chroma at `Oklab.labOf`'s scale. -/
def hueCosMilli (c c' : Ir.Color) : Int :=
  let p := Oklab.labOf c
  let q := Oklab.labOf c'
  let n := Nat.sqrt (Oklab.chromaSq p).toNat * Nat.sqrt (Oklab.chromaSq q).toNat
  if n == 0 then 0 else 1000 * (p.a * q.a + p.b * q.b) / n

def chromaOf (c : Ir.Color) : Nat := Nat.sqrt (Oklab.chromaSq (Oklab.labOf c)).toNat

/-- The code roles: every token type's role by its parent chain, each role's
colour from the document's palette by the stated rule or the style, and one
colour and weight for every type of one role, in both artifacts. -/
def codeRoleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let role (path : String) := Kind.role ⟨path⟩
  t "code roles: a proof hole, a raised not-implemented error and a lexer error are one role"
    (role "Generic.Error" == .error && role "Name.Exception" == .error && role "Error" == .error)
  t "code roles: a type takes its parent's role unless one is named for it"
    (role "Keyword.Type" == .keyword && role "Keyword.Constant" == .literal &&
      role "Name" == .ink && role "Name.Function" == .name && role "Name.Builtin" == .name &&
      role "Name.Function.Magic" == .name && role "Name.Decorator" == .name &&
      role "Name.Namespace" == .name && role "Name.Class" == .name &&
      role "Name.Builtin.Pseudo" == .ink && role "Name.Variable" == .ink &&
      role "Name.Variable.Magic" == .ink && role "Name.Constant" == .literal &&
      role "Literal.Number.Integer" == .literal && role "Literal.String.Doc" == .literal &&
      role "Literal.String.Interpol" == .literal &&
      role "Comment.Single" == .comment && role "Comment.Hashbang" == .comment &&
      role "Comment.Preproc" == .keyword &&
      role "Operator" == .ink && role "Operator.Word" == .keyword && role "Punctuation" == .ink &&
      role "Generic.Prompt" == .keyword && role "Generic.Prompt.VirtualEnv" == .keyword &&
      role "Generic.Output" == .comment && role "Generic.Traceback" == .error &&
      role "Generic.Strong" == .ink && role "Text.Whitespace" == .ink && role "" == .ink)
  let white := Ir.Color.white
  let ink := Ir.Color.ofHtml 0x20 0x24 0x40
  let alert := Ir.Color.ofHtml 0xB0 0x10 0x30
  let muted := Ir.Color.ofHtml 0x5A 0x60 0x68
  let exampleInk := Ir.Color.ofHtml 0x1A 0x6A 0x3A
  let own := Ir.Color.ofHtml 0x70 0x20 0x90
  let pal (entries : List (String × Ir.Color)) : Ir.Palette :=
    entries.foldl (fun p (k, c) => p.declare k c) {}
  let invented := pal [("fg", ink), ("bg", white), ("alert", alert), ("muted", muted),
    ("example", exampleInk)]
  let roles (p : Ir.Palette) := CodeColor.resolve p white .default
  let declared (key : String) (c : Ir.Color) : Option CodeColor.Paint :=
    some { color := c, role := some key, declared := true }
  let r := roles invented
  t "code roles: on its page, a role the document names no colour for ships the palette role it reads"
    (r.get .error == declared "alert" alert && r.get .comment == declared "muted" muted &&
      r.get .literal == declared "example" exampleInk && r.get .ink == none)
  let dark := CodeColor.resolve invented Ir.Color.black .default
  t "code roles: on another ground, the palette role is the code role's own colour to adapt"
    (dark.get .error == some { color := alert, role := some "codeerror", declared := false } &&
      dark.get .literal == some { color := exampleInk, role := some "codeliteral", declared := false })
  t "code roles: keywords and names share a tone of the ink's hue, derived and legible"
    (match r.get .keyword, r.get .name with
      | some k, some n =>
        k.color == n.color && !k.declared && k.role == some "codekeyword" &&
          n.role == some "codename" && hueCosMilli k.color ink ≥ 990 &&
          Contrast.contrastMilli k.color white ≥ CodeColor.codeTone
      | _, _ => false)
  t "code roles: a role's own key wins over the palette role it reads, as declared"
    ((roles (invented.declare "codeerror" own)).get .error ==
      some { color := own, role := some "codeerror", declared := true })
  t "code roles: an ink with no hue of its own sets keywords and names in the ink"
    (let r := roles (invented.declare "fg" (Ir.Color.ofHtml 0x22 0x22 0x22))
     r.get .keyword == none && r.get .name == none)
  let teal := Ir.Color.ofHtml 0x1A 0x50 0x70
  t "code roles: a literal hue within 60° of the ink's leaves keywords in the ink"
    (let r := roles (invented.declare "example" teal |>.declare "fg" (Ir.Color.ofHtml 0x1C 0x3A 0x4A))
     hueCosMilli teal (Ir.Color.ofHtml 0x1C 0x3A 0x4A) ≥ 500 && r.get .keyword == none)
  t "code roles: a muted step that is the ink itself quiets comments to the ink 70:30 into the page"
    ((roles (invented.declare "muted" ink)).get .comment ==
      some { color := ink.mix 70 white, role := some "codecomment", declared := false })
  let literalOf (p : Ir.Palette) := ((roles p).get .literal).map (·.color)
  t "code roles: an example that is the ink derives one more hue, far from the ink's and the alert's"
    (match literalOf (invented.declare "example" ink) with
      | some c => hueCosMilli c ink ≤ 50 && hueCosMilli c alert ≤ 50 &&
          Contrast.contrastMilli c white ≥ CodeColor.codeTone &&
          (roles (invented.declare "example" ink)).get .literal ==
            some { color := c, role := some "codeliteral", declared := false }
      | none => false)
  t "code roles: with the alert the only hue, the literal stands opposite it"
    (match literalOf (pal [("fg", Ir.Color.ofHtml 0x22 0x22 0x22), ("bg", white), ("alert", alert)]) with
      | some c => hueCosMilli c alert ≤ -950
      | none => false)
  let quiet := Ir.Color.ofHtml 0x90 0x60 0x60
  t "code roles: no derived hue is louder than the alert"
    (match (roles (invented.declare "alert" quiet)).get .keyword with
      | some k => chromaOf k.color ≤ chromaOf quiet + chromaOf quiet / 10
      | none => false)
  t "code roles: a palette that declares none of the roles the rule reads takes the style's"
    (Ir.ListingStyle.all.all fun style => ListingHighlight.Role.all.all fun r =>
      ((CodeColor.resolve {} white style).get r).map (·.color) == CodeColor.styleColor style r)
  for theme in Theme.builtin do
    let d := Ir.Design.ofPalette theme.palette
    for ground in [d.bg, d.standout.bg] do
      let r := CodeColor.resolve theme.palette ground .default
      t s!"code roles: {theme.name} on {ground.css}: a declared colour is the palette's, any other ships legible"
        (ListingHighlight.Role.all.all fun role => match r.get role with
          | some p => if p.declared then
              ground == d.bg && p.role.any fun key => theme.palette.find? key == some p.color
            else p.role == some role.key &&
              Contrast.contrastMilli (Listing.defaultInk ground p.color) ground ≥ Contrast.aaText
          | none => true)
  let palette := "\\palette{fg=#202440,bg=#FFFFFF,alert=#B01030,muted=#5A6068,example=#1A6A3A}"
  let some fonts ← serifFacesSet | failures ref "code roles: the serif faces load"
  let source := markerLean ++ "\n" ++ markerPython
  for (label, preamble, style, want) in [("the default style", "", Ir.ListingStyle.default, none),
      ("the friendly style", "\\setminted{style=friendly}", .friendly, none),
      ("an invented palette", palette, .default, some alert),
      ("a role's own key", palette ++ "\\palette{codeerror=#702090}", .default, some own)] do
    let (doc, ds) := markerDoc preamble
    t s!"code roles, {label}: the listings elaborate clean" (ds.all (·.severity != .error))
    let laid := ((glyphPaint (layoutOf fonts doc)).filter fun (c, _) =>
      ShellHighlight.visible c).map fun (c, idx, color) => (c, (idx, color))
    let typed := (htmlLines doc).flatten.filter fun (c, _) => ShellHighlight.visible c
    let pdf (w : String) := ShellHighlight.witnessPaint? source w laid
    let html (w : String) := ShellHighlight.witnessPaint? source w typed
    let one {α : Type} [BEq α] (paint : Option (Array α)) : Option α :=
      paint.bind fun p => p[0]?.bind fun first => if p.all (· == first) then some first else none
    let hole := one (pdf "sorry")
    let raised := one (pdf "NotImplementedError")
    t s!"code roles, {label}: the PDF sets the proof hole and the raised error in one colour and weight"
      (hole.isSome && hole == raised)
    t s!"code roles, {label}: the HTML sets them in one colour and weight"
      ((one (html "sorry")).isSome && one (html "sorry") == one (html "NotImplementedError"))
    t s!"code roles, {label}: their colour is the error role's, and the bold keyword's is not"
      (match hole, one (pdf "theorem") with
        | some (_, c), some (kw, k) =>
          kw == 1 && c != k && some c == Listing.ink doc.palette none .genericError (style := style)
        | _, _ => false)
    if let some w := want then
      t s!"code roles, {label}: the error role ships the document's colour exactly"
        (hole.any (·.2 == w) && (one (html "sorry")).any (hasStr ·.color.get! (HtmlDoc.cssColor w)))
  let formatcom := "\\newcommand{\\codestyle}{}\\setminted{formatcom=\\codestyle}"
  let (_, ds) := markerDoc formatcom
  t "code roles: formatcom is said once, as an info line, and is no warning"
    ((ds.filter fun d => d.code == "N0102" && !d.demoted).size == 1 &&
      (ds.filter fun d => d.code == "N0102").size == 2 &&
      ds.all fun d => d.code != "W0110")
  let (_, lstDs) := elabStr (dvDoc "\\usepackage{listings}"
    "\\begin{lstlisting}[formatcom=\\itshape]\nx\n\\end{lstlisting}")
  t "code roles: formatcom is minted's: a listings key of that name stays unknown"
    (lstDs.any (·.code == "W0110") && lstDs.all (·.code != "N0102"))
  -- The style is read only for a role the palette leaves open: two builds
  -- differing only by the declared style ship one page exactly when the
  -- palette answers every role, and the style is then named as inert.
  let shipped (doc : Ir.Doc) := (glyphPaint (layoutOf fonts doc), htmlLines doc)
  let open_ := "\\palette{fg=#202440,bg=#FFFFFF,muted=#5A6068,example=#1A6A3A}"
  for (label, decl, answered) in [("an invented palette", palette, true),
      ("a palette with no alert", open_, false)] do
    let (friendlyDoc, friendlyDs) := markerDoc (decl ++ "\\setminted{style=friendly}")
    let (defaultDoc, defaultDs) := markerDoc (decl ++ "\\setminted{style=default}")
    let inert := fun (ds : Array Diag) (name : String) =>
      ds.filter fun d => d.code == "W0387" && d.subject == some s!"lstopt:style:{name}"
    t s!"code roles, {label}: the declared style changes the page exactly when a role is left to it"
      ((shipped friendlyDoc == shipped defaultDoc) == answered)
    t s!"code roles, {label}: the style is named as inert exactly when it changes no page"
      ((inert friendlyDs "friendly").size == (if answered then 2 else 0) &&
        (inert defaultDs "default").size == (if answered then 2 else 0) &&
        (inert friendlyDs "friendly").all fun d => d.severity == .warning || d.demoted)
  let redInk := Ir.Color.ofHtml 0x4A 0x14 0x18
  t "code roles: an ink whose hue is the alert's own family leaves keywords in the ink"
    (let r := roles (pal [("fg", redInk), ("bg", white), ("alert", Ir.Color.ofHtml 0xC0 0x10 0x1A)])
     hueCosMilli redInk (Ir.Color.ofHtml 0xC0 0x10 0x1A) ≥ 500 && r.get .keyword == none &&
       r.get .name == none)
  let twin := pal [("fg", ink), ("bg", white), ("alert", ink), ("muted", muted)]
  t "code roles: an alert that is the ink leaves the error role to the style"
    ((roles twin).get .error ==
      (CodeColor.styleColor .default .error).map fun c =>
        { color := c, role := some "codeerror", declared := false })
  t "code roles: a muted step that is the alert quiets comments to the ink 70:30 into the page"
    ((roles (invented.declare "muted" alert)).get .comment ==
      some { color := ink.mix 70 white, role := some "codecomment", declared := false })

end Tests
