module

public import Tests.ListingProvider

public section

open LeanTex.Core

/-! Listing token paint against Pygments' own answers: the oracle
`testdata/oracles/pygments-styles.tsv` holds `style_for_token` and minted's composition for every
standard token type of every shipped style. -/

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

/-- A channel as the LaTeX formatter writes it, `'%.2f' % (v / 255)`; no 8-bit channel lies on a
tie. -/
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

/-- The engine's two readings of one type in the oracle's spelling: Pygments' inheritance, then the
LaTeX formatter's composition. -/
def cellsOf (style : Ir.ListingStyle) (type chain : String) : Array String :=
  let table := CodeColor.table style
  let k := Kind.ofPygments type
  let r := table.resolvedOf k
  let l := table.lookOf k
  #[style.name, type, hexCell (r.color.map (·.1)), bit r.bold, bit r.italic, bit r.underline,
    hexCell r.bgcolor, hexCell r.border, chain, (l.color.map (texRgb ·.1)).getD "-",
    bit l.bold, bit l.italic, bit l.underline, boxCell l.box]

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
  let (_, body, _) := emitIn {} doc .print
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

/-- An invented Lean listing of `#` commands, a `#print` form, `#exit` and an array. -/
def hashSource : String :=
  "#check Nat.succ\n#eval 2 + 2\n#guard 1 + 1 == 2\n#print axioms Nat.add_comm\n#exit\n#[1, 2]\n" ++
    "#guard_msgs in"

def hashDoc (style : Ir.ListingStyle) : Ir.Doc × Array Diag :=
  elabStr (dvDoc ("\\usepackage{minted}\\setminted{style=" ++ style.name ++ "}")
    ("\\begin{minted}{lean4}\n" ++ hashSource ++ "\n\\end{minted}"))

/-- Invented listings that define a function and a class and use them, one per language, beside a
builtin and a parameter. -/
def defsPython : String :=
  "class Basket:\n    pass\n\ndef tally(items):\n    return len(items)\n\nprint(tally(Basket()))"
def defsLean : String := "def tally (n : Nat) : Nat := n + 1\n#eval tally 2"

def defsDoc (preamble : String) : Ir.Doc :=
  (elabStr (dvDoc ("\\usepackage{minted}" ++ preamble)
    ("\\begin{minted}{python}\n" ++ defsPython ++ "\n\\end{minted}\n" ++
     "\\begin{minted}{lean4}\n" ++ defsLean ++ "\n\\end{minted}"))).1

end Tests.ListingStyleTable

namespace Tests

open Tests.ListingStyleTable
open LeanTex.Core.ListingHighlight (Kind)

/-- Every token type of every shipped style is painted as Pygments and minted paint it, in both
artifacts, a style colour shipping unchanged where legible. -/
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
      t s!"code roles: {style.name} {type} ships its role's style colour as the style states it, on {ground.css}"
        (Listing.ink {} (some ground) k (style := style) == CodeColor.styleColor style k.role)
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
  let friendlyRed := Listing.ink {} none .genericError (style := some .friendly)
  t "pygments styles: friendly's Generic.Error ships its own #FF0000"
    (friendlyRed == some (Ir.Color.ofHtml 255 0 0))
  t "pygments styles: default's Generic.Error ships its own #E40000"
    (Listing.ink {} none .genericError (style := some .default) == some (Ir.Color.ofHtml 228 0 0))
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

/-- Two languages' must-not-ship markers, a Lean proof hole and a raised not-implemented error,
under an invented palette. -/
def markerLean : String := "theorem t : True := by\n  sorry"
def markerPython : String := "def f():\n    raise NotImplementedError"

def markerDoc (preamble : String) : Ir.Doc × Array Diag :=
  elabStr (dvDoc ("\\usepackage{minted}" ++ preamble)
    ("\\begin{minted}{lean4}\n" ++ markerLean ++ "\n\\end{minted}\n" ++
     "\\begin{minted}{python}\n" ++ markerPython ++ "\n\\end{minted}"))

/-- Oklab hue geometry over shipped colours: the cosine of the hue angle between two colours in
thousandths, and a colour's chroma. -/
def hueCosMilli (c c' : Ir.Color) : Int :=
  let p := Oklab.labOf c
  let q := Oklab.labOf c'
  let n := Nat.sqrt (Oklab.chromaSq p).toNat * Nat.sqrt (Oklab.chromaSq q).toNat
  if n == 0 then 0 else 1000 * (p.a * q.a + p.b * q.b) / n

def chromaOf (c : Ir.Color) : Nat := Nat.sqrt (Oklab.chromaSq (Oklab.labOf c)).toNat

/-- A listing document's visible code as each artifact paints it. -/
def codePaints (fonts : Font.FontSet) (doc : Ir.Doc) :
    Array (Char × Nat × Ir.Color) × Array (Char × HtmlPaint) :=
  (((glyphPaint (layoutOf fonts doc)).filter fun (c, _) =>
      ShellHighlight.visible c).map fun (c, idx, color) => (c, (idx, color)),
    (htmlLines doc).flatten.filter fun (c, _) => ShellHighlight.visible c)

/-- Lean's `#` commands set as Lean's own highlighter reads them, in both artifacts: each command
and `#print`'s word in the keyword role's colour and weight, `#exit` in the error role's, and an
array's `#[` and the names in the ink. -/
def hashCommandChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "hash commands: the serif faces load"
  for style in Ir.ListingStyle.all do
    let (doc, ds) := hashDoc style
    t s!"hash commands {style.name}: the minted listing elaborates clean"
      (ds.all (·.severity != .error))
    let (laid, typed) := codePaints fonts doc
    let fg := (Ir.Design.ofDoc doc).fg
    let pdf (context word : String) :=
      onePaint (ShellHighlight.namePaint? hashSource context word 0 laid)
    let html (context word : String) :=
      onePaint (ShellHighlight.namePaint? hashSource context word 0 typed)
    let sets (role : ListingHighlight.Role) (kind : Kind) (context word : String) : IO Unit := do
      let (bold, italic) := role.weights
      let ink := Listing.ink doc.palette none kind (style := style)
      t s!"hash commands {style.name}: PDF sets {word} in the {role.word} role's ink and weight"
        (kind.role == role && pdf context word == some (faceOf bold italic, ink.getD fg))
      t s!"hash commands {style.name}: typed HTML sets {word} in the {role.word} role's ink and weight"
        ((html context word).any fun p =>
          p.bold == bold && p.italic == italic && !p.underline && match ink with
            | some c => p.color.any (hasStr · (HtmlDoc.cssColor c))
            | none => p.color.isNone)
    for (context, word) in [("#check", "#check"), ("#eval", "#eval"), ("#guard 1", "#guard"),
        ("#print", "#print"), ("axioms", "axioms"), ("#guard_msgs", "#guard_msgs")] do
      sets .keyword .keyword context word
    sets .error .genericError "#exit" "#exit"
    for word in ["#[", "Nat.add_comm"] do
      sets .ink .text word word

/-- The code roles: every token type's role by its parent chain, each role's colour from the palette
by the stated rule or the style, one colour and weight per role, in both artifacts. -/
def codeRoleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let role (path : String) := Kind.role ⟨path⟩
  t "code roles: each role's style colour is read off a type of that role"
    (ListingHighlight.Role.all.all fun r => (CodeColor.roleStyleKind r).all (·.role == r))
  t "code roles: a proof hole, a raised not-implemented error and a lexer error are one role"
    (role "Generic.Error" == .error && role "Name.Exception" == .error && role "Error" == .error)
  t "code roles: a type takes its parent's role unless one is named for it"
    (role "Keyword.Type" == .keyword && role "Keyword.Constant" == .literal &&
      role "Name" == .ink && role "Name.Function" == .ink && role "Name.Builtin" == .name &&
      role "Name.Function.Magic" == .ink && role "Name.Decorator" == .name &&
      role "Name.Namespace" == .ink && role "Name.Class" == .ink &&
      role "Name.Attribute" == .name &&
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
    entries.foldl (fun p (k, c) => p.declareKey k c) {}
  let invented := pal [("fg", ink), ("bg", white), ("alert", alert), ("muted", muted),
    ("example", exampleInk)]
  let roles (p : Ir.Palette) := CodeColor.resolve p white (some .default)
  let declared (key : Ir.Role) (c : Ir.Color) : Option CodeColor.Paint :=
    some { color := c, role := some key, declared := true }
  let r := roles invented
  t "code roles: on its page, a role the document names no colour for ships the palette role it reads"
    (r.get .error == declared .alert alert && r.get .comment == declared .muted muted &&
      r.get .literal == declared .example exampleInk && r.get .ink == none)
  let dark := CodeColor.resolve invented Ir.Color.black (some .default)
  t "code roles: on another ground, the palette role is the code role's own colour to adapt"
    (dark.get .error == some { color := alert, role := some .codeError, declared := false } &&
      dark.get .literal == some { color := exampleInk, role := some .codeLiteral, declared := false })
  t "code roles: keywords and names share a tone of the ink's hue, derived and legible"
    (match r.get .keyword, r.get .name with
      | some k, some n =>
        k.color == n.color && !k.declared && k.role == some .codeKeyword &&
          n.role == some .codeName && hueCosMilli k.color ink ≥ 990 &&
          Contrast.contrastMilli k.color white ≥ CodeColor.codeTone
      | _, _ => false)
  t "code roles: a role's own key wins over the palette role it reads, as declared"
    ((roles (invented.declare (.role .codeError) own)).get .error ==
      some { color := own, role := some .codeError, declared := true })
  t "code roles: an ink with no hue of its own sets keywords and names in the ink"
    (let r := roles (invented.declare (.role .ink) (Ir.Color.ofHtml 0x22 0x22 0x22))
     r.get .keyword == none && r.get .name == none)
  let teal := Ir.Color.ofHtml 0x1A 0x50 0x70
  t "code roles: a literal hue within 60° of the ink's leaves keywords in the ink"
    (let r := roles (invented.declare (.role .example) teal |>.declare (.role .ink) (Ir.Color.ofHtml 0x1C 0x3A 0x4A))
     hueCosMilli teal (Ir.Color.ofHtml 0x1C 0x3A 0x4A) ≥ 500 && r.get .keyword == none)
  -- A muted step is derived, never a fixed mix: the ink hue's quietest tone at 0.10 above 4.5:1.
  let quietTone (p : Option CodeColor.Paint) : Bool :=
    match p with
    | some q => !q.declared && q.role == some .codeComment && hueCosMilli q.color ink ≥ 990 &&
        Contrast.aaText + 100 ≤ Contrast.contrastMilli q.color white &&
        Contrast.contrastMilli q.color white ≤ Contrast.aaText + 200
    | none => false
  t "code roles: a muted step that is the ink itself quiets comments to the quietest tone of the ink's hue"
    (quietTone ((roles (invented.declare (.role .muted) ink)).get .comment))
  let literalOf (p : Ir.Palette) := ((roles p).get .literal).map (·.color)
  t "code roles: an example that is the ink derives one more hue, far from the ink's and the alert's"
    (match literalOf (invented.declare (.role .example) ink) with
      | some c => hueCosMilli c ink ≤ 50 && hueCosMilli c alert ≤ 50 &&
          Contrast.contrastMilli c white ≥ CodeColor.codeTone &&
          (roles (invented.declare (.role .example) ink)).get .literal ==
            some { color := c, role := some .codeLiteral, declared := false }
      | none => false)
  t "code roles: with the alert the only hue, the literal stands opposite it"
    (match literalOf (pal [("fg", Ir.Color.ofHtml 0x22 0x22 0x22), ("bg", white), ("alert", alert)]) with
      | some c => hueCosMilli c alert ≤ -950
      | none => false)
  let quiet := Ir.Color.ofHtml 0x90 0x60 0x60
  t "code roles: no derived hue is louder than the alert"
    (match (roles (invented.declare (.role .alert) quiet)).get .keyword with
      | some k => chromaOf k.color ≤ chromaOf quiet + chromaOf quiet / 10
      | none => false)
  t "code roles: a palette that declares none of the roles the rule reads takes the style's"
    (Ir.ListingStyle.all.all fun style => ListingHighlight.Role.all.all fun r =>
      ((CodeColor.resolve {} white style).get r).map (·.color) == CodeColor.styleColor style r)
  for theme in Theme.builtin do
    let d := Ir.Design.ofPalette (deckBundle theme)
    for ground in [d.bg, d.standout.bg] do
      let r := CodeColor.resolve (deckBundle theme) ground (some .default)
      t s!"code roles: {theme.name} on {ground.css}: a declared colour is the palette's, any other ships legible"
        (ListingHighlight.Role.all.all fun role => match r.get role with
          | some p => if p.declared then
              ground == d.bg && p.role.any fun key => Ir.Design.declared? (deckBundle theme) key == some p.color
            else p.role == some (Ir.Role.ofCode role) &&
              Contrast.contrastMilli (Listing.fitInk (CodeColor.codeFloor (deckBundle theme) ground)
                ground p.color) ground ≥ CodeColor.codeFloor (deckBundle theme) ground
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
    let (laid, typed) := codePaints fonts doc
    let pdf (w : String) := ShellHighlight.witnessPaint? source w laid
    let html (w : String) := ShellHighlight.witnessPaint? source w typed
    let hole := onePaint (pdf "sorry")
    let raised := onePaint (pdf "NotImplementedError")
    t s!"code roles, {label}: the PDF sets the proof hole and the raised error in one colour and weight"
      (hole.isSome && hole == raised)
    t s!"code roles, {label}: the HTML sets them in one colour and weight"
      ((onePaint (html "sorry")).isSome && onePaint (html "sorry") == onePaint (html "NotImplementedError"))
    t s!"code roles, {label}: their colour is the error role's, and the bold keyword's is not"
      (match hole, onePaint (pdf "theorem") with
        | some (_, c), some (kw, k) =>
          kw == 1 && c != k && some c == Listing.ink doc.palette none .genericError (style := style)
        | _, _ => false)
    if let some w := want then
      t s!"code roles, {label}: the error role ships the document's colour exactly"
        (hole.any (·.2 == w) && (onePaint (html "sorry")).any (hasStr ·.color.get! (HtmlDoc.cssColor w)))
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
  -- The style is read only for a role the palette leaves open, and is otherwise named as inert.
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
        { color := c, role := some .codeError, declared := false, styled := true })
  t "code roles: a muted step that is the alert quiets comments to the quietest tone of the ink's hue"
    (quietTone ((roles (invented.declare (.role .muted) alert)).get .comment))
  -- A retired per-type key is named once and leaves its listing as the document without the key.
  let typed (preamble : String) : Ir.Doc :=
    (elabStr (dvDoc ("\\usepackage{minted}" ++ palette ++ preamble)
      "\\begin{minted}{python}\nprint(\"s\", 1 + len(x))\n\\end{minted}")).1
  let plainTyped := shipped (typed "")
  for r in [ListingHighlight.Role.literal, .name, .ink] do
    t s!"code roles: {Ir.codeKey r} repaints the listing holding each retired key's type"
      (shipped (typed s!"\\palette\{ {Ir.codeKey r} = #AA0000 }") != plainTyped)
  for (key, r) in CodeColor.retiredKeys do
    for spelling in [s!"\\palette\{ {key} = #AA0000 }", s!"\\definecolor\{{key}}\{HTML}\{AA0000}",
        s!"\\colorlet\{{key}}\{black}"] do
      let (_, ds) := markerDoc (palette ++ spelling)
      let named := ds.filter fun d => d.code == "W0387" && d.subject == some s!"listingkey:{key}"
      t s!"code roles: {spelling} is named once where it stands, pointing to {Ir.codeKey r}"
        (named.size == 1 && named.all fun d => hasStr (d.help.getD "") (Ir.codeKey r))
      t s!"code roles: {spelling} leaves the listing holding its type as the document without it"
        (shipped (typed spelling) == plainTyped)
  let (_, early) := elabStr (dvDoc "\\usepackage{minted}"
    "\\textcolor{codestring}{x}\n\n\\palette{codestring = #AA0000}\n\n\\textcolor{codestring}{y}")
  t "code roles: a retired key used before its declaration is still named at full strength"
    (early.any fun d => d.code == "W0387" && !d.demoted && d.help.isSome)
  t "code roles: no shipped bundle declares a retired key"
    (Theme.builtin.all fun th => (deckBundle th).entries.all fun (k, _) =>
      (CodeColor.retiredKeys.lookup k.key).isNone)


/-- A generated palette's code is complete and vivid: keywords, names and literals a quarter turn
apart in one band at the text floor, `CodeColor.roleGap` apart, comments quiet, alike in both artifacts and
the TeX export. -/
def seededCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "seeded code: the serif faces load"
  let source := "@cache\ndef probe(n):\n    # an invented remark\n" ++
    "    raise NotImplementedError(len(\"synthetic\") + 1)"
  let build (seeds more : String) : Ir.Doc × Array Diag :=
    elabStr (dvDeck ("\\usepackage{minted}\n\\palette[seeds]{ " ++ seeds ++ " }\n" ++ more)
      ("\\begin{frame}[fragile]\n\\begin{minted}{python}\n" ++ source ++ "\n\\end{minted}\n\\end{frame}"))
  let paints (doc : Ir.Doc) : List (Option Ir.Color) :=
    let (laid, _) := codePaints fonts doc
    ["def", "len", "synthetic", "remark", "NotImplementedError", "probe"].map fun w =>
      (onePaint (ShellHighlight.witnessPaint? source w laid)).map (·.2)
  let black := "ink = #000000, paper = #FFFFFF, accent = #FACC15"
  let violet := "ink = #2B2440, paper = #FFFFFF, accent = #E85D2A"
  let key (k : String) (r : ListingHighlight.Role) (c : Ir.Color) :
      String × List (ListingHighlight.Role × Ir.Color) :=
    (s!"\\palette\{ {k} = {c.css} }\n", [(r, c)])
  -- A quarter turn, less the rounding of 8-bit colours; and, from the error's hue, less too the
  -- disliked region's width and two degrees, where a slot moves out of it.
  let quarter : Int := 88000
  let moved : Int := 64000
  for (label, seeds, (more, declared), inkHue, spread) in [
      ("a black ink and a yellow accent", black, ("", []), false, quarter),
      ("a neutral ink and a magenta accent", "ink = #1A1A1A, paper = #FFFFFF, accent = #C026D3",
        ("", []), false, quarter),
      ("a violet ink and an orange accent", violet, ("", []), true, quarter),
      ("a teal accent a quarter turn from the disliked yellow-greens",
        "ink = #3B2F2A, paper = #FBF6EC, accent = #0D9488", ("", []), false, moved),
      ("a declared literal", black, key "codeliteral" .literal (Ir.Color.ofHtml 0x15 0x80 0x3D), false,
        quarter),
      ("a declared keyword", black, key "codekeyword" .keyword (Ir.Color.ofHtml 0xBE 0x18 0x5D), false,
        quarter),
      ("a declared keyword at the literal's hue", violet,
        key "codekeyword" .keyword (Ir.Color.ofHtml 0x04 0x78 0x57), false, quarter),
      ("a declared name", black, key "codename" .name (Ir.Color.ofHtml 0x00 0x63 0x44), false, quarter),
      ("a declared error", black, key "codeerror" .error (Ir.Color.ofHtml 0x2B 0x58 0x8C), false,
        quarter),
      ("a declared listing ink", black, key "codeink" .ink (Ir.Color.ofHtml 0x14 0x53 0x2D), false,
        quarter)] do
    let (doc, ds) := build seeds more
    t s!"seeded code, {label}: the listing elaborates clean" (ds.all (·.severity != .error))
    let (_, typed) := codePaints fonts doc
    let html (w : String) := onePaint (ShellHighlight.witnessPaint? source w typed)
    let d := Ir.Design.ofPalette doc.palette
    let alert := Ir.Design.declared? doc.palette .alert
    let muted := Ir.Design.declared? doc.palette .muted
    let floor := Ir.GroundDepth.decks.text
    match paints doc, alert with
    | [some kw, some nm, some lit, some cm, some err, some ink], some al =>
      let shipped : List (ListingHighlight.Role × Ir.Color) :=
        [(.keyword, kw), (.name, nm), (.literal, lit), (.comment, cm), (.error, err), (.ink, ink)]
      let isDeclared (r : ListingHighlight.Role) := declared.any (·.1 == r)
      let derived := ([(ListingHighlight.Role.keyword, kw), (.name, nm), (.literal, lit)].filter
        fun (r, _) => !isDeclared r).map (·.2)
      let held := (declared.filter fun (r, _) => r != .ink && r != .error).map (·.2)
      let coloured := [kw, nm, lit, err]
      t s!"seeded code, {label}: keywords, names and literals each set in a colour of their own"
        ([kw, nm, lit].all (· != d.fg) && [kw, nm, lit].all (· != ink) && kw != nm && nm != lit &&
          kw != lit)
      t s!"seeded code, {label}: each derived one shows a hue"
        (derived.all fun c => Oklab.okJnd ≤ chromaOf c)
      let apart := derived.zipIdx
      t s!"seeded code, {label}: the derived hues stand a quarter turn apart"
        (apart.all fun (c, i) => apart.all fun (c', j) => i == j || quarter ≤ hueGap (hueOf c) (hueOf c'))
      t s!"seeded code, {label}: the derived hues stand from the error's at least the spread its slots allow"
        (derived.all fun c => spread ≤ hueGap (hueOf c) (hueOf err))
      t s!"seeded code, {label}: a derived hue stands an eighth of a turn from a declared one"
        (derived.all fun c => held.all fun c' => 43000 ≤ hueGap (hueOf c) (hueOf c'))
      t s!"seeded code, {label}: each derived one stands at the text floor on the paper, on the gamut's edge, out of the disliked region"
        (decide (0 < floor) && derived.all fun c =>
          let r := Contrast.contrastMilli c d.bg
          decide (floor ≤ r ∧ r < floor + 150) && edgeChroma c ≤ chromaOf c + Oklab.okJnd / 2 &&
            !dislikedBox c)
      t s!"seeded code, {label}: every coloured role stands apart from the ink and from every other"
        ((coloured.zipIdx.all fun (c, i) => coloured.zipIdx.all fun (c', j) =>
            i == j || CodeColor.roleGap * CodeColor.roleGap ≤ ContrastSolve.deltaEOkSq c c') &&
          coloured.all fun c => CodeColor.roleGap * CodeColor.roleGap ≤ ContrastSolve.deltaEOkSq c ink)
      -- Where the alert is the ink on a mark, errors take the mark's hue at the floor.
      let marked := (Ir.Design.declared? doc.palette .alertMark).isSome
      t s!"seeded code, {label}: comments set in the quiet muted step, errors in the alert or the mark's hue"
        (some cm == muted && chromaOf cm < 2 * Oklab.okJnd &&
          (err == al && !marked || isDeclared .error ||
            marked && err != ink && Oklab.okJnd ≤ chromaOf err && !dislikedBox err))
      t s!"seeded code, {label}: a role its own key declares ships as declared"
        (declared.all fun (r, c) => shipped.lookup r == some c)
      t s!"seeded code, {label}: the web page sets each role in the PDF's colour"
        ([("def", kw), ("len", nm), ("synthetic", lit), ("remark", cm), ("NotImplementedError", err)].all
          fun (w, c) => (html w).any fun p => p.color.any (hasStr · (HtmlDoc.cssColor c)))
      if inkHue then
        t s!"seeded code, {label}: keywords take the slot nearest the ink's hue"
          (hueGap (hueOf kw) (hueOf d.fg) ≤ 45000)
      let exported := CodeExport.pageBrushes doc.palette .default
      t s!"seeded code, {label}: the export colours every role but the ink, as the page does"
        ([(ListingHighlight.Role.keyword, kw), (.name, nm), (.literal, lit), (.comment, cm),
          (.error, err)].all fun (r, c) => (exported.get r).ink == some c)
    | _, _ => t s!"seeded code, {label}: every role's token ships in one colour" false
  -- The palette the script builds from the same seeds paints the same code.
  for (label, spelled, ink, accent) in [
      ("a black ink and a yellow accent", black, Ir.Color.ofHtml 0 0 0, Ir.Color.ofHtml 0xFA 0xCC 0x15),
      ("a violet ink and an orange accent", "ink = #2B2440, paper = #FFFFFF, accent = #E85D2A",
        Ir.Color.ofHtml 0x2B 0x24 0x40, Ir.Color.ofHtml 0xE8 0x5D 0x2A)] do
    let seeds : SeedPalette.Seeds := { ink, paper := Ir.Color.white, accent }
    match SeedPalette.generate seeds (seeds.targets .decks) with
    | .error _ => t s!"seeded code, {label}: the seeds generate" false
    | .ok g =>
      let st : SeedPalette.SeedState :=
        { seeds, targets := seeds.targets .decks, blocks := .tonal, colors := g.colors }
      let script := CodeExport.pageBrushes (({} : Ir.Palette).applySeeds st) .default
      let (doc, _) := build spelled ""
      let native := CodeExport.pageBrushes doc.palette .default
      t s!"seeded code, {label}: the script's palette paints the native page's code"
        (ListingHighlight.Role.all.all fun r => (script.get r).ink == (native.get r).ink)
  -- Two inks a channel step apart plan their code alike: keywords take the slot nearest the ink's.
  let (near, _) := build "ink = #2B2440, paper = #FFFFFF, accent = #E85D2A" ""
  let (next, _) := build "ink = #2C2440, paper = #FFFFFF, accent = #E85D2A" ""
  match paints near, paints next with
  | [some kw, some nm, some lit, _, _, _], [some kw', some nm', some lit', _, _, _] =>
    t "seeded code: two inks a step apart set keywords, names and literals in the same hues"
      (hueCosMilli kw kw' ≥ 990 && hueCosMilli nm nm' ≥ 990 && hueCosMilli lit lit' ≥ 990)
  | _, _ => t "seeded code: two inks a step apart ship every role in one colour" false

/-- A name reads alike where its listing defines it and where it uses it, and across languages,
while a builtin keeps the name role. -/
def definitionNameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "definition names: the serif faces load"
  let source := defsPython ++ "\n" ++ defsLean
  -- (what, context, name, visible characters of the context before the name)
  let sites : List (String × String × String × Nat) :=
    [("the Python function's definition", "def tally(items)", "tally", 3),
     ("the Python function's call", "print(tally(Basket", "tally", 6),
     ("the Python class's definition", "class Basket:", "Basket", 5),
     ("the Python class's use", "tally(Basket())", "Basket", 6),
     ("a Python parameter", "return len(items)", "items", 10),
     ("the Lean function's definition", "def tally (n", "tally", 3),
     ("the Lean function's use", "#eval tally 2", "tally", 5)]
  for (label, preamble) in [("the default style", ""),
      ("an invented palette",
        "\\palette{fg=#202440,bg=#FFFFFF,alert=#B01030,muted=#5A6068,example=#1A6A3A}")] do
    let doc := defsDoc preamble
    let (laid, typed) := codePaints fonts doc
    let pdf := sites.map fun (what, context, name, skip) =>
      (what, onePaint (ShellHighlight.namePaint? source context name skip laid))
    let html := sites.map fun (what, context, name, skip) =>
      (what, onePaint (ShellHighlight.namePaint? source context name skip typed))
    let firstPdf := (pdf.head?.bind (·.2))
    let firstHtml := (html.head?.bind (·.2))
    t s!"definition names, {label}: every site is read"
      (pdf.all (·.2.isSome) && html.all (·.2.isSome))
    for ((what, p), (_, h)) in pdf.zip html do
      t s!"definition names, {label}: the PDF sets {what} as the first definition"
        (p.isSome && p == firstPdf)
      t s!"definition names, {label}: the HTML sets {what} as the first definition"
        (h.isSome && h == firstHtml)
    let builtinInk := (Listing.ink doc.palette none .nameBuiltin).getD (Ir.Design.ofDoc doc).fg
    let builtin := onePaint (ShellHighlight.namePaint? source "return len(items)" "len" 6 laid)
    t s!"definition names, {label}: the PDF keeps a builtin's name role paint"
      (builtin.isSome && builtin != firstPdf && builtin.map (·.2) == some builtinInk)
    let typedBuiltin := onePaint (ShellHighlight.namePaint? source "return len(items)" "len" 6 typed)
    t s!"definition names, {label}: the HTML keeps a builtin's name role paint"
      (typedBuiltin.isSome && typedBuiltin != firstHtml &&
        typedBuiltin.any fun p => p.color.any (hasStr · (HtmlDoc.cssColor builtinInk)))

/-- The TeX export of a palette's code colours: one redefinition per standard token type, each
role's colour the one the page paints, and a document reading it builds without a warning. -/
def codeExportChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ink := Ir.Color.ofHtml 0x20 0x24 0x40
  let alert := Ir.Color.ofHtml 0xB0 0x10 0x30
  let pal : Ir.Palette := ({} : Ir.Palette).declare (.role .ink) ink
    |>.declare (.role .page) Ir.Color.white |>.declare (.role .alert) alert
  for style in Ir.ListingStyle.all do
    let tex := CodeExport.texDeclarations "Probe" pal style
    let named := (PygmentsStyle.standardTypes.filter (!·.2.isEmpty)).length
    t s!"code export {style.name}: one macro per standard type"
      ((tex.splitOn "\\@namedef{PYG@tok@").length == named + 1)
    t s!"code export {style.name}: every macro states every setting"
      (((tex.splitOn "\\@namedef{PYG@tok@").drop 1).all fun m =>
        ["\\PYG@bf=", "\\PYG@it=", "\\PYG@ul=\\relax", "\\PYG@bc=\\relax", "\\PYG@tc"].all
          (hasStr m ·))
    let brushes := CodeExport.pageBrushes pal style
    for r in ListingHighlight.Role.all do
      match (brushes.get r).ink with
      | some c =>
        t s!"code export {style.name}: the {repr r} role's colour is the one the page ships"
          (hasStr tex s!"\\definecolor\{{CodeExport.colorName "Probe" r}}\{HTML}\{{Ir.Color.hexByte c.r}{Ir.Color.hexByte c.g}{Ir.Color.hexByte c.b}}")
      | none =>
        t s!"code export {style.name}: the {repr r} role defines no colour of its own"
          (!hasStr tex s!"\\definecolor\{{CodeExport.colorName "Probe" r}}")
    t s!"code export {style.name}: the error role is the palette's alert, exactly"
      ((brushes.get .error).ink == some alert)
    t s!"code export {style.name}: an ink type sets in the listing's own colour"
      (hasStr tex "\\@namedef{PYG@tok@n}{\\let\\PYG@bf=\\relax\\let\\PYG@it=\\relax\\let\\PYG@ul=\\relax\\let\\PYG@bc=\\relax\\let\\PYG@tc=\\relax}")
    t s!"code export {style.name}: a coloured type lets its role's colour command"
      (ListingHighlight.Role.all.all fun r => match (brushes.get r).ink with
        | some _ => hasStr tex ("\\newcommand\\" ++ CodeExport.colorName "Probe" r ++ "Tok[1]{\\textcolor{" ++
            CodeExport.colorName "Probe" r ++ "}{#1}}") &&
          hasStr tex ("\\let\\PYG@tc=\\" ++ CodeExport.colorName "Probe" r ++ "Tok}")
        | none => !hasStr tex (CodeExport.colorName "Probe" r ++ "Tok"))
    let (_, ds) := elabStr (dvDoc ("\\usepackage{minted}\n" ++ tex ++ "\\setminted{formatcom=\\ProbePygments}\n")
      "\\begin{minted}{python}\nx = len(\"probe\") + 1\n\\end{minted}")
    t s!"code export {style.name}: a document that reads the export builds clean ({(ds.filter (·.severity != .note)).map (·.code)})"
      (ds.all (·.severity == .note))

end Tests
