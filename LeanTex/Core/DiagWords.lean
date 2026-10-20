module

namespace LeanTex.Core

/-- The word a message opens with: what is wrong with, or what was done to, the thing it names. -/
public inductive Diag.Qual where
  | undefined
  | unsupported
  | ignored
  | unused
  | invalid
  | unreadable
  | missing
  | duplicate
  | unclosed
  | unexpected
  | substituted
  | overfull
  | illegible
  | failed
  | tight
  | translated
  | resolved
  | default
  deriving Repr, BEq, DecidableEq

public def Diag.Qual.label : Diag.Qual → String
  | .undefined => "undefined"
  | .unsupported => "unsupported"
  | .ignored => "ignored"
  | .unused => "unused"
  | .invalid => "invalid"
  | .unreadable => "unreadable"
  | .missing => "missing"
  | .duplicate => "duplicate"
  | .unclosed => "unclosed"
  | .unexpected => "unexpected"
  | .substituted => "substituted"
  | .overfull => "overfull"
  | .illegible => "illegible"
  | .failed => "failed"
  | .tight => "tight"
  | .translated => "translated"
  | .resolved => "resolved"
  | .default => "default"

public def Diag.Qual.all : List Diag.Qual :=
  [.undefined, .unsupported, .ignored, .unused, .invalid, .unreadable, .missing, .duplicate,
   .unclosed, .unexpected, .substituted, .overfull, .illegible, .failed, .tight, .translated,
   .resolved, .default]

public theorem Diag.Qual.all_complete (q : Diag.Qual) : q ∈ Diag.Qual.all := by
  cases q <;> simp [Diag.Qual.all]

/-- The kind of thing a message names, from one closed vocabulary. -/
public inductive Diag.Noun where
  | command | environment | option | key | value | length | colour | colourModel | package
  | «class» | theme | file | directory | output | image | figure | picture | font | face | family
  | glyph | character | encoding | language | labelKey | reference | citation | entry | field
  | string | style | element | icon | code | pageSize | argument | parameter | signature
  | assertion | group | line | table | row | frame | page | node | measure | heading | title
  | link | anchor | landmark | altText | overlay | conditional | definition | template | math
  | listing | lexer | statement | phrase | resource | standard | pageBox | attribute | ink
  | profile | footnote | marker | text | unit | date | collation | backend | operation
  | expression | division | markup | runningHead | runningFoot | footer | spacing | width
  | numbering | nesting | syntax | covering | seeds | mix | tool | drawing | highlighter | tag
  | target | facts | commit | graph | object | intent | year | mathFont | declaration
  | box | cell | column | counter | note | paragraph | alphabet | weight | symbol | accent
  | address | kind | mode | step | share | rule | skip | gap | margin | size | shape | coordinate
  | path | pattern | layer | arrow | scheme | role | token | comment | header | region | variable
  | slot | record | number | dimension | branch | shortTitle | paragraphBreak | pageStyle
  | frameTitle | titlePage | bibliography | url | level | list | item | contract | fill | space
  | fontSize | locale | hook | stylesheet | entryType | headingLevel | scope | alignment | «float»
  | caption | body | block | display | columnSpec | delimiter | conversion | converter | version
  | property | feature | mark | format | section | annotation | sequence | order | content
  | environmentName | optionalArgument
  deriving Repr, BEq, DecidableEq

public def Diag.Noun.label : Diag.Noun → String
  | .command => "command"
  | .environment => "environment"
  | .option => "option"
  | .key => "key"
  | .value => "value"
  | .length => "length"
  | .colour => "colour"
  | .colourModel => "colour model"
  | .package => "package"
  | .class => "class"
  | .theme => "theme"
  | .file => "file"
  | .directory => "directory"
  | .output => "output"
  | .image => "image"
  | .figure => "figure"
  | .picture => "picture"
  | .font => "font"
  | .face => "face"
  | .family => "family"
  | .glyph => "glyph"
  | .character => "character"
  | .encoding => "encoding"
  | .language => "language"
  | .labelKey => "label"
  | .reference => "reference"
  | .citation => "citation"
  | .entry => "entry"
  | .field => "field"
  | .string => "string"
  | .style => "style"
  | .element => "element"
  | .icon => "icon"
  | .code => "code"
  | .pageSize => "page size"
  | .argument => "argument"
  | .parameter => "parameter"
  | .signature => "signature"
  | .assertion => "assertion"
  | .group => "group"
  | .line => "line"
  | .table => "table"
  | .row => "row"
  | .frame => "frame"
  | .page => "page"
  | .node => "node"
  | .measure => "measure"
  | .heading => "heading"
  | .title => "title"
  | .link => "link"
  | .anchor => "anchor"
  | .landmark => "landmark"
  | .altText => "alt text"
  | .overlay => "overlay"
  | .conditional => "conditional"
  | .definition => "definition"
  | .template => "template"
  | .math => "math"
  | .listing => "listing"
  | .lexer => "lexer"
  | .statement => "statement"
  | .phrase => "phrase"
  | .resource => "resource"
  | .standard => "standard"
  | .pageBox => "page box"
  | .attribute => "attribute"
  | .ink => "ink"
  | .profile => "profile"
  | .footnote => "footnote"
  | .marker => "marker"
  | .text => "text"
  | .unit => "unit"
  | .date => "date"
  | .collation => "collation"
  | .backend => "backend"
  | .operation => "operation"
  | .expression => "expression"
  | .division => "division"
  | .markup => "markup"
  | .runningHead => "running head"
  | .runningFoot => "running foot"
  | .footer => "footer"
  | .spacing => "spacing"
  | .width => "width"
  | .numbering => "numbering"
  | .nesting => "nesting"
  | .syntax => "syntax"
  | .covering => "covering"
  | .seeds => "seeds"
  | .mix => "mix"
  | .tool => "tool"
  | .drawing => "drawing"
  | .highlighter => "highlighter"
  | .tag => "tag"
  | .target => "target"
  | .facts => "facts"
  | .commit => "commit"
  | .graph => "graph"
  | .object => "object"
  | .intent => "output intent"
  | .year => "year"
  | .mathFont => "math font"
  | .declaration => "declaration"
  | .box => "box"
  | .cell => "cell"
  | .column => "column"
  | .counter => "counter"
  | .note => "note"
  | .paragraph => "paragraph"
  | .alphabet => "alphabet"
  | .weight => "weight"
  | .symbol => "symbol"
  | .accent => "accent"
  | .address => "address"
  | .kind => "kind"
  | .mode => "mode"
  | .step => "step"
  | .share => "share"
  | .rule => "rule"
  | .skip => "skip"
  | .gap => "gap"
  | .margin => "margin"
  | .size => "size"
  | .shape => "shape"
  | .coordinate => "coordinate"
  | .path => "path"
  | .pattern => "pattern"
  | .layer => "layer"
  | .arrow => "arrow"
  | .scheme => "scheme"
  | .role => "role"
  | .token => "token"
  | .comment => "comment"
  | .header => "header"
  | .region => "region"
  | .variable => "variable"
  | .slot => "slot"
  | .record => "record"
  | .number => "number"
  | .dimension => "dimension"
  | .branch => "branch"
  | .shortTitle => "short title"
  | .paragraphBreak => "paragraph break"
  | .pageStyle => "page style"
  | .frameTitle => "frame title"
  | .titlePage => "title page"
  | .bibliography => "bibliography"
  | .url => "url"
  | .level => "level"
  | .list => "list"
  | .item => "item"
  | .contract => "contract"
  | .fill => "fill"
  | .space => "space"
  | .fontSize => "font size"
  | .locale => "locale"
  | .hook => "hook"
  | .stylesheet => "stylesheet"
  | .entryType => "entry type"
  | .headingLevel => "heading level"
  | .scope => "scope"
  | .alignment => "alignment"
  | .«float» => "float"
  | .caption => "caption"
  | .body => "body"
  | .block => "block"
  | .display => "display"
  | .columnSpec => "column spec"
  | .delimiter => "delimiter"
  | .conversion => "conversion"
  | .converter => "converter"
  | .version => "version"
  | .property => "property"
  | .feature => "feature"
  | .mark => "mark"
  | .format => "format"
  | .section => "section"
  | .annotation => "annotation"
  | .sequence => "sequence"
  | .order => "order"
  | .content => "content"
  | .environmentName => "environment name"
  | .optionalArgument => "optional argument"

/-- A number at or past the last constructor's index, where `ofNat` saturates. -/
private def Diag.Noun.ceiling : Nat := 4096

/-- Every noun, in declaration order, derived from the type. -/
public def Diag.Noun.all : List Diag.Noun :=
  (List.range ((Diag.Noun.ofNat Diag.Noun.ceiling).ctorIdx + 1)).map Diag.Noun.ofNat

/-- A name as a message prints it: `quoted` when it is not one bare word. -/
public structure Diag.Name where
  text : String
  quoted : Bool
  deriving Repr, BEq

/-- Can `s` stand bare in a message: one nonempty run with no space and no quote. -/
public def Diag.Name.bare (s : String) : Bool :=
  !s.isEmpty && s.all fun c => !c.isWhitespace && c != '\''

/-- A name, bare when it is one word and quoted otherwise. -/
public def Diag.Name.of (s : String) : Diag.Name := { text := s, quoted := !Diag.Name.bare s }

/-- A value the author wrote, always quoted. -/
public def Diag.Name.value (s : String) : Diag.Name := { text := s, quoted := true }

public instance : Coe String Diag.Name := ⟨Diag.Name.of⟩

public def Diag.Name.show (n : Diag.Name) : String :=
  if n.quoted then "'" ++ n.text ++ "'" else n.text

/-- One message in the one form: `qual noun [name] [for [noun] name]`. -/
public structure Diag.Words where
  qual : Diag.Qual
  noun : Diag.Noun
  name : Option Diag.Name := none
  obj : Option (Option Diag.Noun × Diag.Name) := none
  deriving Repr, BEq

public def Diag.Words.render (w : Diag.Words) : String :=
  let name := match w.name with
    | some n => " " ++ n.show
    | none => ""
  let obj := match w.obj with
    | some (some n, x) => " for " ++ n.label ++ " " ++ x.show
    | some (none, x) => " for " ++ x.show
    | none => ""
  w.qual.label ++ " " ++ w.noun.label ++ name ++ obj

end LeanTex.Core
