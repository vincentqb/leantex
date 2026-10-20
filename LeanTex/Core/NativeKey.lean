module

/-! The native declarations' keys, each head's a closed vocabulary. -/

namespace LeanTex.Core.Native

/-- The keys of `\page`. -/
public inductive PageKey where
  | size | width | height | margin | vmargin | hmargin | textwidth | textheight | leading
  | baselineskip | parskip | measure | fontsize | bleed | hyphenate | justify | protrusion
  | expansion | numbers | marks | markGap | markThickness | linenumbers | modulo | furnituregap
  | headsep | footskip | rule | frontRule | cropbox | bleedbox | trimbox | artbox | bottom | tmargin
  | bmargin | vmarginratio | clubpenalty | widowpenalty | brokenpenalty | displaywidowpenalty
  | interlinepenalty | predisplaypenalty | hscale | vscale | lists
  | textheightUnder
  | hmarginratio | twoside | headings | openright | web
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
   ("trimbox", .trimbox), ("artbox", .artbox), ("bottom", .bottom), ("tmargin", .tmargin),
   ("bmargin", .bmargin), ("vmarginratio", .vmarginratio), ("clubpenalty", .clubpenalty),
   ("widowpenalty", .widowpenalty), ("brokenpenalty", .brokenpenalty),
   ("displaywidowpenalty", .displaywidowpenalty), ("interlinepenalty", .interlinepenalty),
   ("predisplaypenalty", .predisplaypenalty),
   ("hscale", .hscale),
   ("vscale", .vscale), ("lists", .lists), ("textheight-under", .textheightUnder),
   ("hmarginratio", .hmarginratio), ("twoside", .twoside), ("headings", .headings),
   ("openright", .openright), ("web", .web)]

public def PageKey.name (k : PageKey) : String := ((PageKey.names.find? (·.2 == k)).map (·.1)).getD ""

public def PageKey.ofName? (n : String) : Option PageKey := PageKey.names.lookup n

/-- Whether an unknown key's help lists the key; LaTeX spellings and riders stay unlisted. -/
public def PageKey.listed : PageKey → Bool
  | .headsep | .footskip | .textwidth | .textheight | .baselineskip | .markGap | .markThickness
  | .modulo | .rule | .frontRule | .cropbox | .bleedbox | .trimbox | .artbox | .bottom | .tmargin
  | .bmargin | .vmarginratio | .clubpenalty | .widowpenalty | .brokenpenalty | .displaywidowpenalty
  | .interlinepenalty | .predisplaypenalty | .hscale | .vscale | .lists | .textheightUnder
  | .hmarginratio | .openright
    => false
  | _ => true

/-- Whether the key places the text block across the page, and so claims that axis as declared. -/
public def PageKey.claimsAcross : PageKey → Bool
  | .size | .width | .margin | .hmargin | .textwidth | .bleed | .hscale => true
  | _ => false

/-- Whether the key places the text block down the page, and so claims that axis as declared; the
kernel's `\textheight` stands under the class's top. -/
public def PageKey.claimsDown : PageKey → Bool
  | .size | .height | .margin | .vmargin | .textheight | .bleed | .tmargin | .bmargin
  | .vmarginratio | .vscale => true
  | _ => false

/-- The keys of `\pdfmeta`. -/
public inductive MetaKey where
  | title | author | subject | keywords | url | image | favicon | language | version | standard
  | intent | intentCondition | intentInfo | intentRegistry | intentComponents | created
  | modified | trapped | outline | outlineOpen | outlineNumbered | pagemode
  deriving DecidableEq, Repr, Inhabited

public def MetaKey.names : List (String × MetaKey) :=
  [("title", .title), ("author", .author), ("subject", .subject), ("keywords", .keywords),
   ("url", .url), ("image", .image), ("favicon", .favicon), ("language", .language),
   ("version", .version), ("standard", .standard), ("intent", .intent),
   ("intent-condition", .intentCondition), ("intent-info", .intentInfo),
   ("intent-registry", .intentRegistry), ("intent-components", .intentComponents),
   ("created", .created), ("modified", .modified), ("trapped", .trapped), ("outline", .outline),
   ("outline-open", .outlineOpen), ("outline-numbered", .outlineNumbered), ("pagemode", .pagemode)]

public def MetaKey.name (k : MetaKey) : String := ((MetaKey.names.find? (·.2 == k)).map (·.1)).getD ""

public def MetaKey.ofName? (n : String) : Option MetaKey := MetaKey.names.lookup n

/-- The metadata keys hyperref's `pdf`-prefixed options give as TeX the elaborator sets as text. -/
public inductive TextMetaKey where
  | title | author | subject | keywords
  deriving DecidableEq, Repr, Inhabited

public def TextMetaKey.key : TextMetaKey → MetaKey
  | .title => .title
  | .author => .author
  | .subject => .subject
  | .keywords => .keywords

public def TextMetaKey.all : List TextMetaKey := [.title, .author, .subject, .keywords]

end LeanTex.Core.Native
