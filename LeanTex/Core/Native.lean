module

public import LeanTex.Core.Parse
public import LeanTex.Core.Decl

/-! The native declarations the surfaces lower into: each head's keys a closed vocabulary, and a
setting carried to the elaborator as one word its entry reader reads back exactly
(`Native.render_parse_exact`). -/

namespace LeanTex.Core.Native

open LeanTex.Core.Parse

/-- The keys of `\page`. -/
public inductive PageKey where
  | size | width | height | margin | vmargin | hmargin | textwidth | textheight | leading
  | baselineskip | parskip | measure | fontsize | bleed | hyphenate | justify | protrusion
  | expansion | numbers | marks | markGap | markThickness | linenumbers | modulo | furnituregap
  | headsep | footskip | rule | frontRule | cropbox | bleedbox | trimbox | artbox | bottom
  deriving DecidableEq, Repr, Inhabited

public def PageKey.names : List (String × PageKey) :=
  [("size", .size), ("width", .width), ("height", .height), ("margin", .margin),
   ("vmargin", .vmargin), ("hmargin", .hmargin), ("textwidth", .textwidth),
   ("textheight", .textheight), ("leading", .leading), ("baselineskip", .baselineskip),
   ("parskip", .parskip), ("measure", .measure), ("fontsize", .fontsize), ("bleed", .bleed),
   ("hyphenate", .hyphenate), ("justify", .justify), ("protrusion", .protrusion),
   ("expansion", .expansion), ("numbers", .numbers), ("marks", .marks), ("mark-gap", .markGap),
   ("mark-thickness", .markThickness), ("linenumbers", .linenumbers), ("modulo", .modulo),
   ("furnituregap", .furnituregap), ("headsep", .headsep), ("footskip", .footskip),
   ("rule", .rule), ("front-rule", .frontRule), ("cropbox", .cropbox), ("bleedbox", .bleedbox),
   ("trimbox", .trimbox), ("artbox", .artbox), ("bottom", .bottom)]

public def PageKey.name (k : PageKey) : String := ((PageKey.names.find? (·.2 == k)).map (·.1)).getD ""

public def PageKey.ofName? (n : String) : Option PageKey := PageKey.names.lookup n

/-- Whether an unknown key's help lists the key; LaTeX spellings and riders stay unlisted. -/
public def PageKey.listed : PageKey → Bool
  | .headsep | .footskip | .textwidth | .textheight | .baselineskip | .markGap | .markThickness
  | .modulo | .rule | .frontRule | .cropbox | .bleedbox | .trimbox | .artbox | .bottom => false
  | _ => true

/-- Whether the key declares the page's physical extent, and so claims the page as declared. -/
public def PageKey.claims : PageKey → Bool
  | .size | .width | .height | .margin | .vmargin | .hmargin | .textwidth | .textheight
  | .bleed => true
  | _ => false

/-- The keys of `\pdfmeta`. -/
public inductive MetaKey where
  | title | author | subject | keywords | url | image | favicon | language | version | standard
  | intent | intentCondition | intentInfo | intentRegistry | intentComponents | created
  | modified | trapped
  deriving DecidableEq, Repr, Inhabited

public def MetaKey.names : List (String × MetaKey) :=
  [("title", .title), ("author", .author), ("subject", .subject), ("keywords", .keywords),
   ("url", .url), ("image", .image), ("favicon", .favicon), ("language", .language),
   ("version", .version), ("standard", .standard), ("intent", .intent),
   ("intent-condition", .intentCondition), ("intent-info", .intentInfo),
   ("intent-registry", .intentRegistry), ("intent-components", .intentComponents),
   ("created", .created), ("modified", .modified), ("trapped", .trapped)]

public def MetaKey.name (k : MetaKey) : String := ((MetaKey.names.find? (·.2 == k)).map (·.1)).getD ""

public def MetaKey.ofName? (n : String) : Option MetaKey := MetaKey.names.lookup n

/-- The keys hyperref's `pdf`-prefixed options give as TeX the elaborator sets as text. -/
public def MetaKey.hyperref : List MetaKey := [.title, .author, .subject, .keywords]

/-- A native setting a surface lowers into: `\page` entries by key, or `\tokens` entries by the
length each names, every value spelled as the declaration grammar reads it. -/
public inductive Setting where
  | page (entries : Array (PageKey × String))
  | tokens (entries : Array (String × String))
  deriving DecidableEq, Repr, Inhabited

namespace Setting

/-- The control a setting's declaration opens with. -/
public def head : Setting → String
  | .page _ => "page"
  | .tokens _ => "tokens"

/-- Each entry's key and value as written. -/
public def pairs : Setting → List (String × String)
  | .page es => es.toList.map fun (k, v) => (k.name, v)
  | .tokens es => es.toList

/-- The declaration's block, its entries joined as an author writes them. -/
public def body (s : Setting) : String := ", ".intercalate (s.pairs.map fun (k, v) => k ++ " = " ++ v)

/-- The declaration as a translation note names it. -/
public def render (s : Setting) : String := "\\" ++ s.head ++ "{ " ++ s.body ++ " }"

/-- Whether an entry's key and value read back from the block, beside any other entries. -/
public def carried (kv : String × String) : Bool := Decl.plainKey kv.1 && Decl.wholeValue kv.2

/-- The setting without the entries its block cannot carry whole. -/
public def kept : Setting → Setting
  | .page es => .page (es.filter fun (k, v) => carried (k.name, v))
  | .tokens es => .tokens (es.filter carried)

/-- The entries `kept` drops, as written. -/
public def dropped (s : Setting) : List (String × String) := s.pairs.filter (!carried ·)

/-- The setting's kept entries as the elaborator reads them: its control and one word holding its
block, never lexed as TeX. -/
public def raws (s : Setting) (pos : Pos) : Array Raw :=
  let body := s.kept.body
  #[.ctrl s.head pos, .group (if body.isEmpty then #[] else #[.word body pos]) pos]

end Setting

end LeanTex.Core.Native
